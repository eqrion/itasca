"""Explicit, kernel-justified canonicalizations for reviewed Interface refactors.

This does not ignore changed consumers. It rewrites only named transparent aliases,
identical record identities and fully applied result eliminators; every surrounding
expression node remains subject to the ordinary exact snapshot comparison.
"""
import copy
import sys
from collections import Counter
from interface_snapshot import digest


def application(expression):
    arguments = []
    while isinstance(expression, list) and expression[:1] == ['app']:
        function, argument = expression[1]
        arguments.append(argument)
        expression = function
    return expression, list(reversed(arguments))


def constant(expression):
    return expression[1][0] if isinstance(expression, list) and expression[:1] == ['const'] else None


def forall_parts(expression):
    if not isinstance(expression, list) or expression[:1] != ['forall']:
        raise ValueError('expected a quantified eliminator type')
    kind, (domain, body) = expression[1]
    return kind, domain, body


def identity(declaration):
    return digest({key: declaration[key] for key in
                   ('kind', 'levels', 'type', 'value', 'reducibility')})


def check_identity(declaration, entry):
    if entry.get('identity_sha256') != identity(declaration):
        raise ValueError('compatibility preimage changed: ' + declaration['name'])
    if not entry.get('kernel_check'):
        raise ValueError('compatibility needs recorded kernel evidence')


def check_alias(declaration, target):
    if (declaration['kind'] != 'definition' or
            declaration['type'] != target['type'] or
            declaration['levels'] != target['levels']):
        raise ValueError('alias type or declaration kind changed: ' + declaration['name'])
    value, typ, count = declaration['value'], declaration['type'], 0
    while isinstance(value, list) and value[:1] == ['lam']:
        kind, (domain, body) = value[1]
        expected_kind, expected_domain, typ = forall_parts(typ)
        if (kind, domain) != (expected_kind, expected_domain):
            raise ValueError('alias binder changed: ' + declaration['name'])
        value, count = body, count + 1
    head, arguments = application(value)
    if (constant(head) != target['name'] or head[1][1] != [] or
            arguments != [['bvar', index] for index in reversed(range(count))]):
        raise ValueError('alias is not the exact reviewed eta expansion: ' + declaration['name'])


def family_members(records, entry):
    old, new = entry['old'], entry['new']
    members = entry['members']
    if len(members) < 2 or members[0] != '' or len(set(members)) != len(members):
        raise ValueError('invalid explicit family members')
    actual = {name for name in records if name == old or name.startswith(old + '.')}
    expected = {old + suffix for suffix in members}
    if actual != expected or records[old]['kind'] != 'inductive':
        raise ValueError('family inventory changed: ' + old)
    constructors = [old + suffix for suffix in members[1:]]
    if (any(records[name]['kind'] != 'constructor' for name in constructors) or
            records[old]['dependencies'][-len(constructors):] != constructors):
        raise ValueError('family constructor order changed: ' + old)
    if not entry.get('kernel_check'):
        raise ValueError('family mapping needs recorded kernel evidence')
    return {old + suffix: new + suffix for suffix in members}


def result_types(declaration):
    if declaration['kind'] != 'definition' or declaration['value'] is None:
        raise ValueError('result eliminator must be a checked definition')
    _, motive_type, remaining = forall_parts(declaration['type'])
    _, result_type, _ = forall_parts(remaining)
    _, motive_domain, _ = forall_parts(motive_type)
    head, types = application(result_type)
    if (motive_domain != result_type or constant(head) != 'Aeneas.Std.core.result.Result'
            or len(types) != 2):
        raise ValueError('unexpected result eliminator domain: ' + declaration['name'])
    # Every reviewed helper is closed over concrete success/error types and has
    # exactly motive, result and the two branch arguments.
    arity, cursor = 0, declaration['type']
    while isinstance(cursor, list) and cursor[:1] == ['forall']:
        _, _, cursor = forall_parts(cursor)
        arity += 1
    if arity != 4:
        raise ValueError('unexpected result eliminator arity: ' + declaration['name'])
    return result_type, types


def canonicalize(before, after, plan):
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000))
    if plan.get('schema') != 1:
        raise ValueError('unknown Interface compatibility schema')
    records = {record['name']: record for record in before['declarations']}
    aliases, families, retired = {}, {}, set()
    for entry in plan['aliases']:
        name, target = entry['name'], entry['target']
        check_identity(records[name], entry)
        check_alias(records[name], records[target])
        aliases[name] = target
        retired.add(name)
    coalescences = []
    for entry in plan['coalescences'] + plan['family_renames']:
        mapping = family_members(records, entry)
        if families.keys() & mapping.keys():
            raise ValueError('overlapping family canonicalizations')
        families.update(mapping)
        if entry in plan['coalescences']:
            coalescences.append(mapping)
            retired.update(mapping)
    helpers = {}
    for entry in plan['result_cases']:
        name = entry['name']
        check_identity(records[name], entry)
        if entry['branch_order'] not in ('success-error', 'error-success'):
            raise ValueError('unknown result branch order')
        result_type, types = result_types(records[name])
        helpers[name] = (result_type, types, entry['branch_order'], entry['application_levels'])
        retired.add(name)
    if len(retired) != plan['retired_reading_records']:
        raise ValueError('retired record count does not match the reviewed plan')
    counts = Counter()

    def old_name(name):
        return families.get(aliases.get(name, name), aliases.get(name, name))

    def normalize(expression, previous):
        if not isinstance(expression, list):
            return expression
        head, arguments = application(expression)
        name = constant(head)
        if name in helpers:
            if not previous or len(arguments) != 4:
                raise ValueError('unreviewed/partial old result eliminator: ' + name)
            result_type, types, order, levels = helpers[name]
            if head[1][1] != levels:
                raise ValueError('result eliminator universe changed: ' + name)
            motive, result, first, second = arguments
            expected = ['lam', ['Lean.BinderInfo.default', [result_type, ['sort', 'Lean.Level.zero']]]]
            if motive != expected:
                raise ValueError('result motive is not exactly constant Prop: ' + name)
            success, error = (first, second) if order == 'success-error' else (second, first)
            counts['old_result_cases'] += 1
            return ['reviewed_result_cases', [normalize(part, True) for part in
                                             [*types, result, success, error]]]
        if name == plan['result_predicate']:
            if previous or len(arguments) != 5 or head[1][1] != []:
                raise ValueError('unexpected new result predicate application')
            counts['new_result_cases'] += 1
            return ['reviewed_result_cases', [normalize(part, False) for part in arguments]]
        if expression[:1] == ['const']:
            current, levels = expression[1]
            return ['const', [old_name(current) if previous else current, copy.deepcopy(levels)]]
        if expression[:1] == ['proj']:
            owner, (index, value) = expression[1]
            return ['proj', [old_name(owner) if previous else owner,
                             [index, normalize(value, previous)]]]
        return [normalize(part, previous) for part in expression]

    fields = ('kind', 'levels', 'type', 'value', 'reducibility', 'dependencies')

    def record_normalization(record, previous):
        result = dict(record)
        if previous:
            result['name'] = old_name(record['name'])
            result['dependencies'] = [old_name(name) for name in record['dependencies']]
        for field in ('type', 'value'):
            result[field] = normalize(record[field], previous)
        return result

    # Retirement of duplicate records is justified by exact constructor and
    # field-type identities, in addition to the separately checked constructive iff.
    for mapping in coalescences:
        for old, target in mapping.items():
            previous = record_normalization(records[old], True)
            canonical = record_normalization(records[target], True)
            if any(previous[field] != canonical[field] for field in fields):
                raise ValueError('coalesced records differ: ' + old)
    counts.clear()
    old_records = [record_normalization(record, True) for record in before['declarations']
                   if record['name'] not in retired]
    new_records = [record_normalization(record, False) for record in after['declarations']]
    if len({record['name'] for record in old_records}) != len(old_records):
        raise ValueError('unreviewed declaration collision after canonicalization')
    expected = plan['result_case_applications']
    if counts['old_result_cases'] != expected or counts['new_result_cases'] != expected:
        raise ValueError('result case application count changed: ' + str(dict(counts)))
    report = {'retired_records': sorted(retired), 'applications': dict(counts),
              'preserved_original_records': len(old_records)}
    return dict(before, declarations=old_records), dict(after, declarations=new_records), report

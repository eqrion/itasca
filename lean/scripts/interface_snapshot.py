#!/usr/bin/env python3
"""Prepare and compare elaborated interface snapshots, never source approximations.

Export with ITASCA_AUDIT_JSON=... lake env lean scripts/Audit.lean first.
The raw export is authoritative; SHA256 digests supplement readable expressions.
"""
import argparse
import hashlib
import gzip
import difflib
import tempfile
import sys
import json
from pathlib import Path
from interface_metadata import annotate_metadata
from audit_environment import collect_audit


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()



def prepare(data):
    annotate_metadata(data)
    for d in data['declarations']:
        # Keep raw serialization hashes even when a future ownership move requires
        # an individually reviewed auxiliary-name mapping.
        d['identity_sha256'] = digest({k: d[k] for k in ('kind', 'levels', 'type', 'value', 'reducibility')})
    return data


def load(path):
    raw = path.read_bytes()
    if path.suffix == '.gz':
        raw = gzip.decompress(raw)
    return json.loads(raw)


def closure_escapes(data):
    escaped = []
    for declaration in data['declarations']:
        owner, kind = declaration['module'], declaration['kind']
        if not owner.startswith('Itasca.') or owner.startswith(('Itasca.Results.Definitions.', 'Itasca.Generated.')):
            continue
        if kind == 'axiom' or (kind == 'theorem' and owner.startswith('Itasca.Results.')):
            continue
        escaped.append(declaration['name'])
    return escaped


def canonicalize(data, mappings):
    replacements = {}
    for entry in mappings:
        old, new = entry['old'], entry['new']
        if not old.startswith('_private.') or not new.startswith('_private.'):
            raise ValueError('auxiliary mapping cannot rename an explicit public declaration')
        tail = entry['parent'] + '.' + entry['role']
        if not old.endswith('.' + tail) or not new.endswith('.' + tail):
            raise ValueError('auxiliary mapping changes the preserved parent or role')
        if not entry.get('reason'):
            raise ValueError('auxiliary mapping needs an individual recorded reason')
        replacements[old] = new

    return map_strings(data, lambda value: replacements.get(value, value))


def rename_declarations(data, renames):
    """Apply an explicit reviewed declaration rename before exact comparison.

    Every old name must exist and destinations must be injective, including names
    left unchanged. Only entire names are replaced: expression structure, literal
    contents, universe parameters, binder kinds and constructor order stay exact.
    This is separate from private ownership/hygiene mappings.
    """
    names = {d['name'] for d in data['declarations']}
    if not isinstance(renames, dict) or any(
            not isinstance(old, str) or not isinstance(new, str) or not new
            for old, new in renames.items()):
        raise ValueError('declaration renames must map old names to nonempty new names')
    unknown = set(renames) - names
    if unknown:
        raise ValueError('rename source absent from baseline: ' + ', '.join(sorted(unknown)))
    if len({renames.get(name, name) for name in names}) != len(names):
        raise ValueError('declaration renames collide with another baseline declaration')
    return map_strings(data, lambda value: renames.get(value, value))


def map_strings(data, rewrite):
    def shallow(value):
        if isinstance(value, str):
            return rewrite(value)
        if isinstance(value, list):
            return [None] * len(value)
        if isinstance(value, dict):
            return {}
        return value

    result = shallow(data)
    pending = [(data, result)]
    while pending:
        old, new = pending.pop()
        items = old.items() if isinstance(old, dict) else enumerate(old)
        for key, value in items:
            new[key] = shallow(value)
            if isinstance(value, (dict, list)):
                pending.append((value, new[key]))
    return result



def canonicalize_generated_universes(before, after, mappings):
    """Alpha-map only compiler hygiene in generated noConfusion universe binders.

    Declaration names, binder positions, scope IDs, explicit universe names and
    all other expression nodes remain exact. Raw snapshot hashes are untouched.
    """
    old = {d['name']: d for d in before['declarations']}
    current = {d['name']: d for d in after['declarations']}
    result = dict(before, declarations=list(before['declarations']))
    positions = {d['name']: index for index, d in enumerate(result['declarations'])}
    for entry in mappings:
        name = entry['declaration']
        if name not in old and name not in current:
            continue  # Recorded helper outside this comparison scope.
        if name not in old or name not in current:
            raise ValueError(f'missing generated-universe declaration: {name}')
        previous, following = old[name], current[name]
        parent = name.rsplit('.', 1)[0]
        old_parent, new_parent = old.get(parent), current.get(parent)
        if (not name.endswith(('.noConfusion', '.noConfusionType')) or
                not old_parent or not new_parent or
                old_parent['kind'] != 'inductive' or new_parent['kind'] != 'inductive' or
                previous.get('range') not in (None, old_parent.get('range')) or
                following.get('range') not in (None, new_parent.get('range')) or
                previous.get('parent') != parent or following.get('parent') != parent):
            raise ValueError('universe exemption is restricted to generated noConfusion helpers')
        index = entry['parameter_index']
        old_name, new_name = entry['old'], entry['new']
        old_owner, new_owner = entry['old_owner'], entry['new_owner']
        if (not isinstance(index, int) or index < 0 or index >= len(previous['levels']) or
                entry.get('parent') != parent or not entry.get('role') or
                len(previous['levels']) != len(following['levels']) or
                previous['levels'][index] != old_name or following['levels'][index] != new_name or
                previous['module'] != old_owner or following['module'] != new_owner):
            raise ValueError('generated universe count/order/ownership changed')
        head, separator, counter = old_name.partition('._hygCtx._hyg.')
        scope = head.rsplit('.', 1)[-1]
        if (not separator or not counter.isdigit() or not scope.isdigit() or
                head != f'v._@.{old_owner}.{scope}' or
                new_name != f'v._@.{new_owner}.{scope}._hygCtx._hyg.{counter}' or
                not entry.get('reason')):
            raise ValueError('explicit universe name or hygiene scope changed')
        old_token, new_token = f'`v.«_@».{old_owner} {scope}', f'`v.«_@».{new_owner} {scope}'
        def rewrite(value):
            if value == old_name:
                return new_name
            if value.startswith('Lean.Level.') and '_hygCtx' in value:
                return value.replace(old_token, new_token)
            return value
        result['declarations'][positions[name]] = map_strings(
            result['declarations'][positions[name]], rewrite)
    return result


def compare(before, after):
    old = {d['name']: d for d in before['declarations']}
    new = {d['name']: d for d in after['declarations']}
    errors = [f'missing declaration requested by export: {name}' for name in after.get('missing', [])]
    if sorted(before['roots']) != sorted(after['roots']):
        errors.append('public root registry changed')
    for name, d in old.items():
        if name not in new:
            errors.append(f'missing declaration: {name}')
            continue
        fields = ['kind', 'levels', 'type', 'value', 'reducibility']
        if d['kind'] == 'inductive':
            # The exported dependency tail lists every constructor in order.
            # Comparing it catches added/reordered constructors even when the
            # current export was requested using only baseline member names.
            fields.append('dependencies')
        for field in fields:
            if d[field] != new[name][field]:
                errors.append(f'{name}: changed {field}')
                old_text = json.dumps(d[field], indent=2, ensure_ascii=False).splitlines()
                new_text = json.dumps(new[name][field], indent=2, ensure_ascii=False).splitlines()
                errors.extend(difflib.unified_diff(old_text, new_text,
                              fromfile=f'baseline/{name}/{field}',
                              tofile=f'current/{name}/{field}', n=3))
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--compare', type=Path)
    parser.add_argument('--auxiliary-map', type=Path)
    parser.add_argument('--generated-universe-map', type=Path)
    parser.add_argument('--declaration-renames', type=Path,
                        help='explicit reviewed old/new declaration names; all other identity fields stay exact')
    parser.add_argument('--compatibility-map', type=Path,
                        help='explicit kernel-checked alias/record/result-case canonicalizations')
    parser.add_argument('--export', action='store_true', help='run compiled Lean environment audit')
    parser.add_argument('--require-interface', action='store_true',
                        help='final G gate: reject any handwritten semantic cone escape')
    args = parser.parse_args()
    if args.export:
        with tempfile.TemporaryDirectory(prefix='itasca-audit-') as directory:
            path = Path(directory) / 'current.json'
            collect_audit(Path.cwd(), Path(directory), full_export=path)
            data = prepare(load(path))
    elif args.input:
        data = prepare(load(args.input))
    else:
        parser.error('provide input or --export')
    if args.output:
        raw = (json.dumps(data, sort_keys=True, separators=(',', ':')) + '\n').encode()
        args.output.write_bytes(gzip.compress(raw, mtime=0)
                                if args.output.suffix == '.gz' else raw)
    if args.require_interface:
        escapes = closure_escapes(data)
        if escapes:
            raise SystemExit('handwritten reading declarations outside Interface/Results:\n' + '\n'.join(escapes))
    if args.compare:
        before = load(args.compare)
        if args.declaration_renames:
            before = rename_declarations(before, load(args.declaration_renames))
        if args.auxiliary_map:
            before = canonicalize(before, load(args.auxiliary_map))
        if args.generated_universe_map:
            before = canonicalize_generated_universes(before, data, load(args.generated_universe_map))
        if args.compatibility_map:
            from interface_compatibility import canonicalize as canonicalize_compatibility
            plan = load(args.compatibility_map)
            predicate = Path(__file__).resolve().parent.parent / 'Itasca/Results/Definitions/RustResult.lean'
            if hashlib.sha256(predicate.read_bytes()).hexdigest() != plan['checked_predicate_source_sha256']:
                raise ValueError('result predicate source differs from kernel-checked compatibility evidence')
            before, data, report = canonicalize_compatibility(before, data, plan)
            print('Reviewed compatibility: ' + json.dumps(report, sort_keys=True))
        errors = compare(before, data)
        if errors:
            raise SystemExit('\n'.join(errors))
        print(f"preserved {len(data['roots'])} public types and all baseline declarations")


if __name__ == '__main__':
    main()

import copy
import unittest

from interface_compatibility import canonicalize, identity
from interface_snapshot import compare


def const(name, levels=None):
    return ['const', [name, levels or []]]


def app(function, *arguments):
    for argument in arguments:
        function = ['app', [function, argument]]
    return function


def binder(tag, domain, body):
    return [tag, ['Lean.BinderInfo.default', [domain, body]]]


PROP = ['sort', 'Lean.Level.zero']


def declaration(name, kind, typ, value=None, dependencies=None):
    return dict(name=name, kind=kind, levels=[], type=typ, value=value,
                reducibility='abbrev' if kind == 'definition' else None,
                dependencies=dependencies or [])


def plan():
    return dict(schema=1, aliases=[], coalescences=[], family_renames=[], result_cases=[],
                result_predicate='Itasca.RustResultPost', result_case_applications=0,
                retired_reading_records=0)


class CompatibilityTests(unittest.TestCase):
    def alias_fixture(self):
        typ = declaration('T', 'inductive', PROP, dependencies=['T.mk'])
        ctor = declaration('T.mk', 'constructor', const('T'), dependencies=['T'])
        alias = declaration('Alias', 'definition', PROP, const('T'), ['T'])
        root = declaration('Root', 'theorem', app(const('And'), const('Alias'), const('Guard')))
        before = dict(roots=['Root'], declarations=[typ, ctor, alias, root])
        after = copy.deepcopy(before)
        after['declarations'].remove(after['declarations'][2])
        after['declarations'][-1]['type'] = app(const('And'), const('T'), const('Guard'))
        config = plan()
        config.update(aliases=[dict(name='Alias', target='T', identity_sha256=identity(alias),
                                    kernel_check='fixture')], retired_reading_records=1)
        return before, after, config

    def test_alias_does_not_waive_a_consumer_guard(self):
        before, after, config = self.alias_fixture()
        old, new, _ = canonicalize(before, after, config)
        self.assertEqual(compare(old, new), [])
        after['declarations'][-1]['type'] = const('T')
        old, new, _ = canonicalize(before, after, config)
        self.assertTrue(any('changed type' in error for error in compare(old, new)))

    def test_alias_value_must_be_exact_even_with_a_new_fingerprint(self):
        before, after, config = self.alias_fixture()
        alias = before['declarations'][2]
        alias['value'] = app(const('And'), const('T'), const('False'))
        config['aliases'][0]['identity_sha256'] = identity(alias)
        with self.assertRaisesRegex(ValueError, 'exact reviewed eta expansion'):
            canonicalize(before, after, config)

    def test_promoting_an_alias_to_its_inductive_has_no_rename_cycle(self):
        before, _, config = self.alias_fixture()
        config['family_renames'] = [dict(old='T', new='Alias', members=['', '.mk'],
                                         kernel_check='fixture')]
        after = copy.deepcopy(before)
        typ, ctor, _, root = after['declarations']
        typ.update(name='Alias', dependencies=['Alias.mk'])
        ctor.update(name='Alias.mk', type=const('Alias'), dependencies=['Alias'])
        after['declarations'] = [typ, ctor, root]
        old, new, _ = canonicalize(before, after, config)
        self.assertEqual(compare(old, new), [])

    def coalescence_fixture(self):
        canonical = declaration('T', 'inductive', PROP, dependencies=['T.mk'])
        duplicate = declaration('D', 'inductive', PROP, dependencies=['D.mk'])
        ctor = declaration('T.mk', 'constructor', const('T'), dependencies=['T'])
        copied = declaration('D.mk', 'constructor', const('D'), dependencies=['D'])
        root = declaration('Root', 'theorem', app(const('And'), const('D'), const('Guard')))
        before = dict(roots=['Root'], declarations=[canonical, ctor, duplicate, copied, root])
        after = copy.deepcopy(before)
        after['declarations'] = [after['declarations'][i] for i in [0, 1, 4]]
        after['declarations'][-1]['type'] = app(const('And'), const('T'), const('Guard'))
        config = plan()
        config.update(coalescences=[dict(old='D', new='T', members=['', '.mk'],
                                         kernel_check='fixture')], retired_reading_records=2)
        return before, after, config

    def test_coalescence_requires_identical_constructor_fields(self):
        before, after, config = self.coalescence_fixture()
        old, new, _ = canonicalize(before, after, config)
        self.assertEqual(compare(old, new), [])
        before['declarations'][3]['type'] = app(const('And'), const('D'), const('False'))
        with self.assertRaisesRegex(ValueError, 'coalesced records differ'):
            canonicalize(before, after, config)

    def test_unlisted_family_constructor_is_rejected(self):
        before, after, config = self.coalescence_fixture()
        before['declarations'].append(declaration('D.extra', 'constructor', const('D')))
        with self.assertRaisesRegex(ValueError, 'family inventory changed'):
            canonicalize(before, after, config)

    def test_partial_result_eliminator_is_rejected(self):
        before, after, config = self.result_fixture()
        expression = before['declarations'][1]['type'][1][1][1]
        before['declarations'][1]['type'][1][1][1] = expression[1][0]
        with self.assertRaisesRegex(ValueError, 'partial old result eliminator'):
            canonicalize(before, after, config)

    def result_fixture(self):
        nat = const('Nat')
        result = app(const('Aeneas.Std.core.result.Result'), nat, nat)
        motive = binder('forall', result, ['sort', 'Lean.Level.param `u_1'])
        success_type = binder('forall', nat, app(['bvar', 2],
                              app(const('Aeneas.Std.core.result.Result.Ok'), nat, nat, ['bvar', 0])))
        error_type = binder('forall', nat, app(['bvar', 3],
                            app(const('Aeneas.Std.core.result.Result.Err'), nat, nat, ['bvar', 0])))
        typ = binder('forall', motive, binder('forall', result,
                     binder('forall', success_type, binder('forall', error_type,
                     app(['bvar', 3], ['bvar', 2])))))
        helper = declaration('Old.match_1', 'definition', typ, const('FixtureCases'))
        helper['levels'] = ['u_1']
        levels = ['Lean.Level.succ (Lean.Level.zero)']
        success = binder('lam', nat, const('True'))
        error = binder('lam', nat, const('False'))
        args = [binder('lam', result, PROP), ['bvar', 0], success, error]
        root = declaration('Root', 'theorem', binder('forall', result,
                           app(const('Old.match_1', levels), *args)))
        before = dict(roots=['Root'], declarations=[helper, root])
        after = dict(roots=['Root'], declarations=[copy.deepcopy(root)])
        after['declarations'][0]['type'] = binder('forall', result,
            app(const('Itasca.RustResultPost'), nat, nat, ['bvar', 0], success, error))
        config = plan()
        config.update(result_cases=[dict(name='Old.match_1', branch_order='success-error',
                    application_levels=levels, identity_sha256=identity(helper), kernel_check='fixture')],
                    retired_reading_records=1, result_case_applications=1)
        return before, after, config

    def test_result_cases_preserve_branch_order(self):
        before, after, config = self.result_fixture()
        old, new, _ = canonicalize(before, after, config)
        self.assertEqual(compare(old, new), [])
        # Both payload types are Nat: swapping predicates is type-correct but wrong.
        body = after['declarations'][0]['type'][1][1][1]
        function, error = body[1]
        prefix, success = function[1]
        after['declarations'][0]['type'][1][1][1] = app(prefix, error, success)
        old, new, _ = canonicalize(before, after, config)
        self.assertTrue(any('changed type' in error for error in compare(old, new)))

    def test_nonconstant_motive_and_changed_universe_are_rejected(self):
        for change in ('motive', 'universe'):
            before, after, config = self.result_fixture()
            expression = before['declarations'][1]['type'][1][1][1]
            while expression[0] == 'app':
                function, argument = expression[1]
                if function[0] == 'const':
                    if change == 'motive':
                        expression[1][1] = binder('lam', argument[1][1][0], const('False'))
                    else:
                        function[1][1] = ['Lean.Level.zero']
                    break
                expression = function
            with self.assertRaises(ValueError):
                canonicalize(before, after, config)

    def test_changed_helper_preimage_is_rejected(self):
        before, after, config = self.result_fixture()
        before['declarations'][0]['value'] = const('DifferentCases')
        with self.assertRaisesRegex(ValueError, 'preimage changed'):
            canonicalize(before, after, config)


if __name__ == '__main__':
    unittest.main()

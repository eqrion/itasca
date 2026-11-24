import copy
import unittest
from interface_snapshot import compare, prepare, closure_escapes, canonicalize, canonicalize_generated_universes, rename_declarations


class SnapshotTests(unittest.TestCase):
    def fixture(self):
        return {'roots': ['Itasca.public'], 'declarations': [{
            'name': 'Itasca.public', 'module': 'Itasca.Results.Test',
            'kind': 'theorem', 'levels': [], 'type': ['const', 'Nat'],
            'value': None, 'reducibility': None, 'range': None,
        }]}

    def test_owner_move_is_not_semantic_change(self):
        old = self.fixture()
        new = copy.deepcopy(old)
        new['declarations'][0]['module'] = 'Itasca.Results.Definitions.Test'
        self.assertEqual(compare(old, new), [])

    def test_missing_is_not_equal(self):
        old = self.fixture()
        new = copy.deepcopy(old)
        new['declarations'] = []
        self.assertIn('missing declaration', compare(old, new)[0])

    def test_expression_change_rejected(self):
        old = self.fixture()
        new = copy.deepcopy(old)
        new['declarations'][0]['type'] = ['const', 'Int']
        self.assertIn('changed type', compare(old, new)[0])

    def test_new_result_requires_review(self):
        old = self.fixture()
        new = copy.deepcopy(old)
        new['roots'].append('Itasca.newResult')
        self.assertIn('public root registry changed', compare(old, new))

    def test_explicit_rename_preserves_expression_structure(self):
        before = self.fixture()
        before['declarations'][0]['type'] = ['const', 'Itasca.public']
        after = rename_declarations(before, {'Itasca.public': 'Itasca.renamed'})
        self.assertEqual(after['roots'], ['Itasca.renamed'])
        self.assertEqual(after['declarations'][0]['type'], ['const', 'Itasca.renamed'])
        after['declarations'][0]['type'] = ['const', 'Int']
        self.assertTrue(compare(rename_declarations(before, {'Itasca.public': 'Itasca.renamed'}), after))

    def test_explicit_rename_rejects_missing_sources_and_collisions(self):
        before = self.fixture()
        with self.assertRaisesRegex(ValueError, 'absent'):
            rename_declarations(before, {'Itasca.missing': 'Itasca.renamed'})
        before['declarations'].append(dict(before['declarations'][0], name='Itasca.other'))
        with self.assertRaisesRegex(ValueError, 'collide'):
            rename_declarations(before, {'Itasca.public': 'Itasca.other'})

    def test_new_semantic_leak_detected(self):
        data = self.fixture()
        data['declarations'].append(dict(data['declarations'][0],
            name='Itasca.leaked', module='Itasca.Support.Helper',
            kind='definition', root=False))
        self.assertEqual(closure_escapes(data), ['Itasca.leaked'])
        data['declarations'][-1]['module'] = 'Itasca.Results.Definitions.Helper'
        self.assertEqual(closure_escapes(data), [])

    def test_auxiliary_map_cannot_rename_public_name(self):
        with self.assertRaises(ValueError):
            canonicalize(self.fixture(), [dict(old='Itasca.public', new='Itasca.other',
                parent='Itasca', role='public', reason='not allowed')])

    def test_auxiliary_map_preserves_private_role(self):
        old = '_private.Old.0.Itasca.Ns.helper'
        new = '_private.New.0.Itasca.Ns.helper'
        mapping = [dict(old=old, new=new, parent='Itasca.Ns', role='helper', reason='move')]
        self.assertEqual(canonicalize({'name': old}, mapping), {'name': new})
        mapping[0]['role'] = 'different'
        with self.assertRaises(ValueError):
            canonicalize({'name': old}, mapping)

    def test_auxiliary_mapping_handles_deep_expression_trees(self):
        value = 'unchanged'
        for _ in range(1500):
            value = [value]
        mapped = canonicalize(value, [])
        for _ in range(1500):
            mapped = mapped[0]
        self.assertEqual(mapped, 'unchanged')

    def universe_fixture(self):
        old_name = 'v._@.Itasca.Old.42._hygCtx._hyg.6'
        new_name = 'v._@.Itasca.Results.Definitions.Old.42._hygCtx._hyg.6'
        record = dict(name='Itasca.Enum.noConfusion', parent='Itasca.Enum', range=None,
                      module='Itasca.Old', levels=[old_name], kind='definition', dependencies=[],
                      type=['sort', 'Lean.Level.param `v.«_@».Itasca.Old 42 _hygCtx'],
                      value=['const', 'Itasca.Old.publicConstant', []], reducibility='regular:1')
        before = dict(roots=[], declarations=[record,
            dict(record, name='Itasca.Enum', kind='inductive', parent=None,
                 levels=[], type=['sort', 'Lean.Level.zero'], value=None, reducibility=None)])
        after = copy.deepcopy(before)
        after['declarations'][0].update(module='Itasca.Results.Definitions.Old', levels=[new_name],
            type=['sort', 'Lean.Level.param `v.«_@».Itasca.Results.Definitions.Old 42 _hygCtx'])
        entry = dict(declaration=record['name'], parent='Itasca.Enum', role='universe binder 0',
                     parameter_index=0, old=old_name, new=new_name,
                     old_owner=record['module'], new_owner=after['declarations'][0]['module'],
                     reason='generated ownership hygiene')
        return before, after, entry

    def test_generated_universe_hygiene_keeps_constants_and_raw_snapshot(self):
        before, after, entry = self.universe_fixture()
        mapped = canonicalize_generated_universes(before, after, [entry])
        self.assertEqual(compare(mapped, after), [])
        self.assertEqual(before['declarations'][0]['levels'], [entry['old']])
        self.assertEqual(mapped['declarations'][0]['value'][1], 'Itasca.Old.publicConstant')

    def test_generated_universe_scope_change_rejected(self):
        before, after, entry = self.universe_fixture()
        entry['new'] = entry['new'].replace('.42.', '.43.')
        after['declarations'][0]['levels'] = [entry['new']]
        with self.assertRaises(ValueError):
            canonicalize_generated_universes(before, after, [entry])

    def test_explicit_universe_change_rejected(self):
        before, after, entry = self.universe_fixture()
        entry.update(old='u', new='v')
        before['declarations'][0]['levels'] = ['u']
        after['declarations'][0]['levels'] = ['v']
        with self.assertRaises(ValueError):
            canonicalize_generated_universes(before, after, [entry])

    def test_generated_universe_map_ignores_only_absent_both_scope(self):
        before, after, entry = self.universe_fixture()
        empty = dict(roots=[], declarations=[])
        self.assertEqual(canonicalize_generated_universes(empty, empty, [entry]), empty)
        after['declarations'] = after['declarations'][1:]
        with self.assertRaisesRegex(ValueError, 'missing generated-universe declaration'):
            canonicalize_generated_universes(before, after, [entry])

    def test_generated_universe_map_rejects_explicit_same_named_helper(self):
        before, after, entry = self.universe_fixture()
        before['declarations'][0]['range'] = dict(start=[5, 1], end=[6, 1])
        with self.assertRaisesRegex(ValueError, 'restricted to generated'):
            canonicalize_generated_universes(before, after, [entry])

    def test_added_constructor_cannot_hide_outside_requested_members(self):
        before = self.fixture()
        declaration = before['declarations'][0]
        declaration.update(kind='inductive', dependencies=['Itasca.public.mk'])
        after = copy.deepcopy(before)
        after['declarations'][0]['dependencies'].append('Itasca.public.newConstructor')
        self.assertTrue(any('changed dependencies' in error for error in compare(before, after)))

    def test_results_matcher_location_uses_owner_not_parent_or_namespace(self):
        data = self.fixture()
        data['declarations'][0].update(name='Itasca.metadata.validate_module.spec.match_1',
            parent='Itasca.metadata.validate_module.spec', kind='definition', root=False,
            module='Itasca.Results.Definitions.Results.Validate')
        self.assertEqual(closure_escapes(data), [])
        data['declarations'][0]['module'] = 'Itasca.Results.Validate'
        self.assertEqual(closure_escapes(data), ['Itasca.metadata.validate_module.spec.match_1'])

    def test_encountered_lemma_statement_cannot_escape_to_implementation(self):
        data = self.fixture()
        data['declarations'][0].update(name='Itasca.Runtime.lemma', root=False,
                                       module='Itasca.Runtime.Implementation', kind='theorem')
        self.assertEqual(closure_escapes(data), ['Itasca.Runtime.lemma'])
        for allowed in ['Itasca.Results.Definitions.Store', 'Itasca.Results.Invoke']:
            data['declarations'][0]['module'] = allowed
            self.assertEqual(closure_escapes(data), [])

    def test_semantic_definition_cannot_hide_in_support_or_subject(self):
        data = self.fixture()
        data['declarations'][0].update(name='Itasca.predicate', kind='definition', root=False)
        for owner in ['Itasca.Results.Support.Hidden', 'Itasca.Results.Validate']:
            data['declarations'][0]['module'] = owner
            self.assertEqual(closure_escapes(data), ['Itasca.predicate'])
        data['declarations'][0]['module'] = 'Itasca.Results.Definitions.Exposed'
        self.assertEqual(closure_escapes(data), [])

    def test_theorem_statement_cannot_hide_in_implementation(self):
        data = self.fixture()
        data['declarations'][0]['module'] = 'Itasca.Runtime.Validation'
        self.assertEqual(closure_escapes(data), ['Itasca.public'])

    def test_hash_is_deterministic(self):
        self.assertEqual(prepare(self.fixture()), prepare(self.fixture()))

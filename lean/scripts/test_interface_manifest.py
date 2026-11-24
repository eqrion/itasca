import copy
import unittest
from interface_manifest import join_metadata


def declaration(name='Itasca.kept', owner='Itasca.Results.Definitions.Source', reading=True):
    return dict(name=name, name_identity='exact-name-constructor-identity', module=owner,
                range=dict(start=[12, 3], end=[16, 1]), parent=None,
                category='handwritten', kind='definition', root=False,
                reading=reading, dependencies=[])


class CurrentManifestTests(unittest.TestCase):
    def test_origin_join_never_overwrites_current_owner_or_range(self):
        current = declaration()
        data = dict(roots=[], declarations=[current])
        origins = dict(module_origins={current['module']: 'Itasca.Old.Source'},
                       declaration_labels={current['name']: dict(module='Itasca.Old.Source',
                           range=dict(start=[999, 1]), closure='elaboration-only')})
        result = join_metadata(data, origins)['declarations'][0]
        self.assertEqual(result['module'], 'Itasca.Results.Definitions.Source')
        self.assertEqual(result['range']['start'], [12, 3])
        self.assertEqual(result['origin_module'], 'Itasca.Old.Source')
        self.assertEqual(result['closure'], 'reading')

    def test_private_support_name_identity_and_reason_are_preserved(self):
        current = declaration('_private.Itasca.Results.Definitions.Support.Source.0.helper',
                              'Itasca.Results.Definitions.Support.Source', False)
        current['range'] = None
        reason = 'required source-shape proof'
        origins = dict(module_origins={current['module']: 'Itasca.Old.Source'},
            declaration_labels={current['name']: dict(closure='elaboration-only',
                                                     placement_reason=reason)})
        result = join_metadata(dict(roots=[], declarations=[current]), origins)['declarations'][0]
        self.assertEqual(result['name_identity'], 'exact-name-constructor-identity')
        self.assertEqual(result['placement_reason'], reason)
        self.assertTrue(result['elaboration_prerequisite'])

    def test_unknown_explicit_vocabulary_is_not_called_required_elaboration(self):
        result = join_metadata(dict(roots=[], declarations=[declaration(reading=False)]), {})
        self.assertEqual(result['declarations'][0]['closure'], 'interface-vocabulary')
        self.assertFalse(result['declarations'][0]['elaboration_prerequisite'])

    def test_interface_vocabulary_remains_separate(self):
        item = declaration(reading=False)
        labels = {item['name']: dict(closure='interface-vocabulary')}
        result = join_metadata(dict(roots=[], declarations=[item]), dict(declaration_labels=labels))
        self.assertEqual(result['declarations'][0]['closure'], 'interface-vocabulary')

    def test_full_identity_trees_cannot_enter_permanent_index_metadata(self):
        record = declaration()
        record['type'] = ['const', 'Nat', []]
        with self.assertRaisesRegex(ValueError, 'slim export'):
            join_metadata(dict(roots=[], declarations=[record]), {})

    def test_missing_or_ambiguous_declaration_metadata_fails_closed(self):
        with self.assertRaises(ValueError):
            join_metadata(dict(roots=['missing'], declarations=[]), {})
        with self.assertRaises(ValueError):
            join_metadata(dict(roots=[], declarations=[declaration(), declaration()]), {})

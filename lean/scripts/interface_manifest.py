#!/usr/bin/env python3
"""Join current elaborated metadata with permanent, reviewable origin labels.

This module never copies historical module/range fields over current fields.
Origin attribution and non-reading classification are separate metadata only.
"""
from interface_metadata import annotate_metadata


def join_metadata(data, origins):
    if any('type' in d or 'value' in d for d in data['declarations']):
        raise ValueError('permanent metadata must use the slim export, not full identity expression trees')
    if data.get('missing'):
        raise ValueError('metadata export contains missing declarations')
    annotate_metadata(data)
    module_origins = origins.get('module_origins', {})
    labels = origins.get('declaration_labels', {})
    seen = set()
    for declaration in data['declarations']:
        name = declaration['name']
        if name in seen:
            raise ValueError(f'ambiguous declaration display identity: {name}')
        seen.add(name)
        label = labels.get(name, {})
        owner = declaration['module']
        declaration['origin_module'] = label.get('origin_module', module_origins.get(owner, owner))
        if declaration.get('reading') or declaration.get('root'):
            declaration['closure'] = 'reading'
        elif owner.startswith('Itasca.Results.Definitions.'):
            if label.get('closure') in ('elaboration-only', 'interface-vocabulary'):
                declaration['closure'] = label['closure']
                declaration['placement_reason'] = label.get('placement_reason', '')
            elif declaration.get('parent') or declaration.get('range') is None:
                declaration['closure'] = 'elaboration-only'
                declaration['placement_reason'] = 'Generated member emitted with its public definition; not in the public semantic reading closure.'
            else:
                declaration['closure'] = 'interface-vocabulary'
                declaration['placement_reason'] = 'Public vocabulary outside the currently registered public reading closure.'
            declaration['elaboration_prerequisite'] = declaration['closure'] == 'elaboration-only'
        else:
            declaration['closure'] = 'foundation'
        if owner == 'Itasca.Generated.FunsExternal':
            declaration['foundation'] = 'handwritten-trusted-model'
        elif declaration.get('category') in ('external', 'spectec', 'specext', 'extracted'):
            declaration['foundation'] = declaration['category']
    missing_roots = set(data['roots']) - seen
    if missing_roots:
        raise ValueError(f'missing public root metadata: {sorted(missing_roots)}')
    return data

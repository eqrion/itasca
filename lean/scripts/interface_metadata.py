"""Shared declaration metadata; independent of migration snapshots and CLI tools."""

def annotate_metadata(data):
    declarations = data['declarations']
    groups = {}
    for d in declarations:
        if d['range']:
            key = (d['module'], tuple(d['range']['start']))
            groups.setdefault(key, []).append(d)
    for group in groups.values():
        explicit = [d for d in group if not d['name'].startswith('_private.')]
        parent = min(explicit or group, key=lambda d: (len(d['name']), d['name']))['name']
        for d in group:
            if not d.get('parent') and d['name'] != parent:
                d['parent'] = parent
    by_name = {d['name']: d for d in declarations}
    for d in declarations:
        if d['range'] is None and not d.get('parent'):
            parts = d['name'].split('.')
            for count in range(len(parts) - 1, 0, -1):
                candidate = '.'.join(parts[:count])
                if candidate in by_name:
                    d['parent'] = candidate
                    d['generated_role'] = '.'.join(parts[count:])
                    break
        elif d.get('parent') and d['name'].startswith(d['parent'] + '.'):
            d['generated_role'] = d['name'][len(d['parent']) + 1:]
    return data

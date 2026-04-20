def generate_payloads(application_handles):
    import hashlib

    def chunk_dict(data_dict, chunk_size):
        for i in range(0, len(data_dict), chunk_size):
            yield data_dict[i:i + chunk_size]

    # Current list of resource_v4_local entries in DB
    resource_v4_local_list_new = []
    resource_v4_local_list_old = ResourceV4Local.objects.filter(
        Affiliation__exact="access-ci.org"
    ).order_by("-CreationTime")

    for chunk in chunk_dict(application_handles, 250):
        for application in chunk:
            cider = CiderInfrastructure.objects.filter(
                info_resourceid=application.ResourceID
            ).first()
            environment_id = application.ID
            environment_id_utf8 = environment_id.encode('utf-8')
            environment_id_hash = f"urn:ogf.org:glue2:access-ci.org:executable.software:{hashlib.md5(environment_id_utf8).hexdigest()}"

            validity = application.ApplicationEnvironment.Validity
            if validity:
                validity = str(validity.total_seconds())

            # Build EntityJSON for the software entity
            entity_json = {
                "ID": environment_id_hash,
                "Category": application.ApplicationEnvironment.EntityJSON.get("Category", None),
                "CreationTime": application.ApplicationEnvironment.CreationTime.isoformat(),
                "Default": application.ApplicationEnvironment.EntityJSON.get("Default", True),
                "Description": application.ApplicationEnvironment.Description,
                "HandleKey": application.Value,
                "HandleType": application.Type,
                "Keywords": application.ApplicationEnvironment.EntityJSON.get("Keywords", None),
                "LocalID": environment_id,
                "Name": application.ApplicationEnvironment.AppName,
                "SupportContact": application.ApplicationEnvironment.EntityJSON.get("SupportContact", "https://support.access-ci.org/help-ticket"),
                "SupportStatus": application.ApplicationEnvironment.EntityJSON.get("SupportStatus", "production"),
                "URL": application.ApplicationEnvironment.EntityJSON.get("URL", None),
                "Validity": validity,
                "Version": application.ApplicationEnvironment.AppVersion,

                # Cider fields
                "Info_GroupID": cider.other_attributes.get("groups", [])[0]["info_groupid"] if len(cider.other_attributes.get("groups", [])) else None,
                "Info_GroupName": cider.other_attributes.get("groups", [])[0]["name"] if len(cider.other_attributes.get("groups", [])) else None,
                "Info_ResourceID": cider.info_resourceid,
                "Info_ResourceName": cider.resource_descriptive_name,
                "Organization_ID": cider.info_siteid,
                "Organization_Name": cider.other_attributes.get("organizations", [])[0]["organization_name"],
            }

            # Build ResourceV4Local entry
            resource_v4_local_entry = {
                "ID": environment_id_hash,
                "Affiliation": "access-ci.org",
                "CatalogMetaURL": "urn:ogf.org:glue2:access-ci.org:catalog:glue2:executable.software",
                "CreationTime": application.ApplicationEnvironment.CreationTime.isoformat(),
                "LocalID": environment_id,
                "LocalType": "GLUE2 Executable Software",
                "LocalURL": f"https://operations-api.access-ci.org/wh2/glue2/v1/software_full/ID/{environment_id}/",
                "Validity": validity,
                "EntityJSON": entity_json,
            }
            resource_v4_local_list_new.append(resource_v4_local_entry)

    payload = {
        # List of items that were added/removed/updated since last run
        # Returns a payload with the above keys
        **compare_dict_lists(
            resource_v4_local_list_old.values(),
            resource_v4_local_list_new,
        ),
    }
    return payload


def compare_dict_lists(
    old_list,
    new_list,
    id_key="LocalID",
    ignore_fields=None,
):
    """
    Compare two lists of dicts with:
    - nested field diff output
    - dot-notation ignore_fields support
    - optimized for large datasets
    - returns only the new value in 'changes'
    """

    if ignore_fields is None:
        ignore_fields = [
            "CreationTime",
            "ID",
            "LocalID",
            "Validity",
            "EntityJSON.CreationTime",
            "EntityJSON.ID",
            "EntityJSON.LocalID",
            "EntityJSON.Validity",
        ]

    ignore_fields = set(ignore_fields)

    # -----------------------------
    # Fast ignore matcher
    # -----------------------------
    def should_ignore(path):
        return any(path == f or path.startswith(f + ".") for f in ignore_fields)

    # -----------------------------
    # Merge a change into a nested dictionary
    # -----------------------------
    def merge_change(d, path_list, value):
        key = path_list[0]
        if len(path_list) == 1:
            d[key] = value  # only new value
        else:
            if key not in d:
                d[key] = {}
            merge_change(d[key], path_list[1:], value)

    # -----------------------------
    # Recursive diff engine
    # -----------------------------
    def deep_diff_nested(old, new, path="", changes=None):
        if changes is None:
            changes = {}

        if old is new:
            return changes

        if type(old) != type(new):
            merge_change(changes, path.split(".") if path else [], new)
            return changes

        if isinstance(old, dict):
            all_keys = old.keys() | new.keys()
            for key in all_keys:
                current_path = f"{path}.{key}" if path else key

                if should_ignore(current_path):
                    continue

                if key not in old:
                    merge_change(changes, current_path.split("."), new[key])
                elif key not in new:
                    merge_change(changes, current_path.split("."), None)
                else:
                    deep_diff_nested(old[key], new[key], current_path, changes)

            return changes

        if isinstance(old, list):
            if len(old) != len(new):
                merge_change(changes, path.split(".") if path else [], new)
                return changes
            for idx, (o, n) in enumerate(zip(old, new)):
                deep_diff_nested(o, n, f"{path}[{idx}]", changes)
            return changes

        # Primitive values
        if old != new:
            merge_change(changes, path.split(".") if path else [], new)

        return changes

    # -----------------------------
    # Lookup dicts for fast O(n) matching
    # -----------------------------
    old_dict = {item[id_key]: item for item in old_list}
    new_dict = {item[id_key]: item for item in new_list}

    old_ids = set(old_dict)
    new_ids = set(new_dict)

    added = [new_dict[_id] for _id in new_ids - old_ids]
    removed = list(old_ids - new_ids)

    updated = []
    for _id in old_ids & new_ids:
        changes = deep_diff_nested(old_dict[_id], new_dict[_id])
        if changes:
            updated.append({
                "LocalID": _id,
                "changes": changes
            })

    return {
        "added": added,
        "removed": removed,
        "updated": updated
    }

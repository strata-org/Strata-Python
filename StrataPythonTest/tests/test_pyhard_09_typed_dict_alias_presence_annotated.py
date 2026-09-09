# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
from typing import NotRequired, TypedDict


class Settings(TypedDict):
    service: str
    retries: NotRequired[int]


# L9 pyhard[summary direct_update] returns={int}; escapes={}
# L9 pyhard[type parameter] assert/assume conforms(settings, Settings); boundary nondet over 17 closed tags
# L9 pyhard[type parameter] assert/assume conforms(retries, int); boundary nondet over 17 closed tags
# L9 pyhard[shape typed_dict_parameter] assert/assume shape_Settings(settings)
def direct_update(settings: Settings, retries: int) -> int:
    # L10 pyhard[flow direct_update in] retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external})
    # L10 pyhard[flow direct_update out] retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external})
    # L10 pyhard[read direct_update.retries@27] binding=definitely_bound
    # L10 pyhard[read direct_update.settings@5] binding=definitely_bound
    # L10 pyhard[type typed_dict_field_write] assert/assume conforms(Settings['retries'], int); observed={bool, int}
    # L10 pyhard[shape typed_dict_field_write] assert/assume shape_Settings(settings); key='retries'
    # L10 pyhard[dispatch settings['retries']] assert/assume key in {Settings}
    # L10 pyhard[row {Settings}] typed_dict_field_write_checked; result={NoneType}
    settings["retries"] = retries
    # L11 pyhard[flow direct_update in] retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external})
    # L11 pyhard[flow direct_update out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external})
    # L11 pyhard[read direct_update.settings@12] binding=definitely_bound
    # L11 pyhard[type return] assert/assume conforms(result, int); observed={int}
    # L11 pyhard[dispatch settings.get('retries')] assert/assume key in {Settings}
    # L11 pyhard[row {Settings}] invoke_typed_dict_method; owner=dict; label=pyhard.typeddict.Settings.get; result={int}; specialized-by=literal key, presence, and argument contracts
    return settings.get("retries")


# L14 pyhard[summary alias_update] returns={int}; escapes={}
# L14 pyhard[type parameter] assert/assume conforms(settings, Settings); boundary nondet over 17 closed tags
# L14 pyhard[type parameter] assert/assume conforms(retries, int); boundary nondet over 17 closed tags
# L14 pyhard[shape typed_dict_parameter] assert/assume shape_Settings(settings)
def alias_update(settings: Settings, retries: int) -> int | None:
    # L15 pyhard[flow alias_update in] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external})
    # L15 pyhard[flow alias_update out] alias -> (binding=definitely_bound; tags={Settings}; defs={assignment:L15:C5}; present={service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}); aliases may={alias~settings} must={alias~settings}
    # L15 pyhard[read alias_update.settings@13] binding=definitely_bound
    alias = settings
    # L16 pyhard[flow alias_update in] alias -> (binding=definitely_bound; tags={Settings}; defs={assignment:L15:C5}; present={service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}); aliases may={alias~settings} must={alias~settings}
    # L16 pyhard[flow alias_update out] alias -> (binding=definitely_bound; tags={Settings}; defs={assignment:L15:C5}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}); aliases may={alias~settings} must={alias~settings}
    # L16 pyhard[read alias_update.retries@24] binding=definitely_bound
    # L16 pyhard[read alias_update.alias@5] binding=definitely_bound
    # L16 pyhard[type typed_dict_field_write] assert/assume conforms(Settings['retries'], int); observed={bool, int}
    # L16 pyhard[shape typed_dict_field_write] assert/assume shape_Settings(alias); key='retries'
    # L16 pyhard[dispatch alias['retries']] assert/assume key in {Settings}
    # L16 pyhard[row {Settings}] typed_dict_field_write_checked; result={NoneType}
    alias["retries"] = retries
    # L17 pyhard[flow alias_update in] alias -> (binding=definitely_bound; tags={Settings}; defs={assignment:L15:C5}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}); aliases may={alias~settings} must={alias~settings}
    # L17 pyhard[flow alias_update out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), alias -> (binding=definitely_bound; tags={Settings}; defs={assignment:L15:C5}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}), retries -> (binding=definitely_bound; tags={bool, int}; defs={param:retries}), settings -> (binding=definitely_bound; tags={Settings}; defs={param:settings}; present={retries, service}; points-to={boundary:alias_update, boundary:direct_update, boundary:external}); aliases may={alias~settings} must={alias~settings}
    # L17 pyhard[read alias_update.settings@12] binding=definitely_bound
    # L17 pyhard[type return] assert/assume conforms(result, NoneType | int); observed={int}
    # L17 pyhard[dispatch settings.get('retries')] assert/assume key in {Settings}
    # L17 pyhard[row {Settings}] invoke_typed_dict_method; owner=dict; label=pyhard.typeddict.Settings.get; result={int}; specialized-by=literal key, presence, and argument contracts
    return settings.get("retries")

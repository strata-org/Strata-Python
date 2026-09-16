from typing import Dict


def top_level_int_dict(Data: Dict[int, str]) -> None:
    """Statement-form: top-level Dict[int, _] quantifier is rejected."""
    for v in Data.values():
        assert len(v) >= 1, 'this assertion is dropped'


def expr_form_int_dict(Data: Dict[int, str]) -> None:
    """Expression-form: all() over Dict[int, _] is rejected."""
    assert all(len(v) >= 1 for v in Data.values()), 'unsupported key domain'

from typing import Dict


def top_level_int_dict(Data: Dict[int, str]) -> None:
    """Statement-form: top-level Dict[int, _] quantifier warns and proceeds."""
    for v in Data.values():
        assert len(v) >= 1, 'this assertion is dropped'


def expr_form_int_dict(Data: Dict[int, str]) -> None:
    """Expression-form: all() over Dict[int, _] warns and proceeds."""
    assert all(len(v) >= 1 for v in Data.values()), 'dropped by warn-and-proceed'

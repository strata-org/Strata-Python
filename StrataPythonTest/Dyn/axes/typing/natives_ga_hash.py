from typing import List, Dict, Union, Optional
print(hash(List[int]) == hash(List[int]), hash(Dict[str, int]) == hash(Dict[str, int]))
print(hash(Union[int, str]) == hash(Union[str, int]), hash(Optional[int]) == hash(Union[None, int]))

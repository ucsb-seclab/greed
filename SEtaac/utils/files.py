from collections import defaultdict
from typing import List, Mapping, Union


def load_csv(path: str, seperator: str='\t') -> List[Union[str, List[str]]]:
    with open(path) as f:
        return [line.split(seperator) for line in f.read().splitlines()]


def load_csv_map(path: str, seperator: str='\t', reverse: bool=False) -> Mapping[str, str]:
    return {y: x for x, y in load_csv(path, seperator)} if reverse else {x: y for x, y in load_csv(path, seperator)}


def load_csv_multimap(path: str, seperator: str='\t', reverse: bool=False) -> Mapping[str, List[str]]:
    ret = defaultdict(list)

    if reverse:
        for y, x in load_csv(path, seperator):
            ret[x].append(y)
    else:
        for x, y in load_csv(path, seperator):
            ret[x].append(y)

    return ret

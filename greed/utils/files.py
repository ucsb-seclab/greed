from collections import defaultdict
from typing import List, Mapping, Union

# Union[str, List[str]] means that the elements within the lists can be either of type str or List[str]
def load_csv(path: str, seperator: str='\t') -> List[Union[str, List[str]]]:
    with open(path) as f:
        # First split each row into its own element, then split columns into its own element [[x1, y1], x2, [x3, y3], [x4, y4, z4]]
        return [line.split(seperator) for line in f.read().splitlines()]

def load_csv_map(path: str, seperator: str='\t', reverse: bool=False) -> Mapping[str, str]:
    return {y: x for x, y in load_csv(path, seperator)} if reverse else {x: y for x, y in load_csv(path, seperator)}

# '\t' probably denotes a separation in columns within a CSV file
def load_csv_multimap(path: str, seperator: str='\t', reverse: bool=False) -> Mapping[str, List[str]]:
    # I'm assuming that this is just a normal dictionary where its values are of type list
    ret = defaultdict(list)

    if reverse:
        for y, x in load_csv(path, seperator):
            ret[x].append(y)
    else:
        for x, y in load_csv(path, seperator):
            ret[x].append(y)

    return ret

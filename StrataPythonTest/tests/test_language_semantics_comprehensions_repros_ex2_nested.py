# EXAMPLE 2 -- nested comprehension, two generators, two filters.
# C model: ex2_nested.c
from typing import TypedDict, List

class Node(TypedDict):
    weight: int

class Cluster(TypedDict):
    size: int
    nodes: List[Node]

class ClustersResponse(TypedDict):
    clusters: List[Cluster]

def list_clusters() -> ClustersResponse:
    return {
        "clusters": [
            {"size": 40, "nodes": [{"weight": 20}]},
            {
                "size": 60,
                "nodes": [{"weight": 5}, {"weight": 11}, {"weight": 20}],
            },
        ]
    }

def main() -> None:
    resp = list_clusters()
    loads = [c['size'] + n['weight']
             for c in resp['clusters'] if c['size'] > 50
             for n in c['nodes'] if n['weight'] > 10]
    assert len(loads) >= 0

main()

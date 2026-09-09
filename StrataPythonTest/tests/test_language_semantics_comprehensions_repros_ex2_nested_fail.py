# Negative pair: the selected nested elements make the result nonempty.
from typing import List, TypedDict


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
            {"size": 60, "nodes": [{"weight": 5}, {"weight": 11}, {"weight": 20}]}
        ]
    }


def main() -> None:
    clusters = list_clusters()["clusters"]
    loads = [
        cluster["size"] + node["weight"]
        for cluster in clusters
        if cluster["size"] > 50
        for node in cluster["nodes"]
        if node["weight"] > 10
    ]
    assert len(loads) == 0


main()

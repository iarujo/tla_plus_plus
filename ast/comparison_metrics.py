from src.spec import Spec
from time import sleep

def compare_asts_aux(nodes1: int, nodes2: int, string1: str, string2: str):
    """
    Compares two asts based on their length and content.

    Args:
        nodes1 (int): The node count of the first AST.
        nodes2 (int): The node count of the second AST.
        string1 (str): The first spec's code.
        string2 (str): The second spec's code.

    Returns:
        dict: A dictionary containing comparison results.
    """
    comparison_results = {
        "length_string1": len(string1),
        "length_string2": len(string2),
        "length_difference": abs(len(string1) - len(string2)),
        "length_difference_percentage": (abs(len(string1) - len(string2)) / max(len(string1), len(string2))) * 100 if max(len(string1), len(string2)) > 0 else 0,
        "are_lengths_equal": len(string1) == len(string2),
        "are_strings_equal": string1 == string2,
        "are_node_counts_equal": nodes1 == nodes2,
        "node_count_difference": abs(nodes1 - nodes2),
        "node_count_difference_percentage": (abs(nodes1 - nodes2) / max(nodes1, nodes2)) * 100 if max(nodes1, nodes2) > 0 else 0,
    }
    return comparison_results


def compare_asts(original: Spec, compiled: Spec):
    """
    Compares two ASTs based on their structure and content.

    Args:
        ast1 (AST): The first AST to compare.
        ast2 (AST): The second AST to compare.
        
    """
    string1 = repr(original)
    string2 = repr(compiled)
    
    print("Original AST:")
    print(string1)
    
    print("\nCompiled AST:")
    print(string2)
    
    nodes1 = original.get_node_count()
    nodes2 = compiled.get_node_count()
    print(f'Node count original: {nodes1}')
    print(f'Node count compiled: {nodes2}')
    
    comparison_results = compare_asts_aux(nodes1, nodes2, string1, string2)
    
    print("Comparison Results:")
    for key, value in comparison_results.items():
        print(f"{key}: {value}")

from src.spec import Spec

def compare_strings(string1, string2):
    """
    Compares two strings based on their length and content.

    Args:
        string1 (str): The first string to compare.
        string2 (str): The second string to compare.

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
        "common_characters": set(string1) & set(string2),
        "unique_to_string1": set(string1) - set(string2),
        "unique_to_string2": set(string2) - set(string1),
    }
    return comparison_results


def compare_asts(ast1: Spec, ast2: Spec):
    """
    Compares two ASTs based on their structure and content.

    Args:
        ast1 (AST): The first AST to compare.
        ast2 (AST): The second AST to compare.
        
    """
    
    original = repr(ast1)
    compiled = repr(ast2)
    
    print("Original AST:")
    print(original)
    
    print("\nCompiled AST:")
    print(compiled)
    
    comparison_results = compare_strings(original, compiled)
    
    print("Comparison Results:")
    for key, value in comparison_results.items():
        print(f"{key}: {value}")

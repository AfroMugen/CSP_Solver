import sys
# import time
from copy import deepcopy
from typing import List, Dict

class CSP():
    def __init__(self, variables: list, domains: Dict[int, List], constraints: Dict[int, List], forward_check: bool):
        self.variables = variables
        self.domains = domains
        self.constraints = constraints
        self.arcs = self.get_arcs()
        self.forward_check = forward_check
        self.calls_to_backtrack = 0

    def get_arcs(self):
        """
        Gets arcs for CSP.

        Helper function that returns a list of all valid arcs for CSP.

        Parameters
        ----------
        self : CSP
            Current CSP object

        Returns
        -------
        List[tuple]
            List of arcs or tuple pairs of variables that share a constraint

        """
        arcs = []
        for variable in self.constraints:
            for constraint in self.constraints[variable]:
                if len(constraint[0]) == 2:
                    arcs.append(constraint[0])

        return arcs

    def back_track(self, assignment: Dict[int, int] = {}):
        """
        Main CSP solving function. Performs Backtracking Search.

        Uses backtracking to attempt to find a valid assignment for the CSP object.

        Parameters
        ----------
        self : CSP
            Current CSP object
        assignment : Dict[int, int]
            Assignment dictionary

        Returns
        -------
        Dict[int, int]/boolean
            Returns Assignment dictionary of valid assignments or False if no valid assignment
            could be found.

        """
        # print("\n\033[91mCurrent assignment:\033[0m %s" % assignment)

        # Base case. Check complete assignment
        self.calls_to_backtrack += 1
        if len(assignment) == len(self.variables):
            return assignment

        var = self.select_unassigned_var(assignment)
        # print("\033[93mProcessing variable:\033[0m %s" % var)
        for value in self.get_ordered_domain(var):
            # print("Trying value: %s..." % value)
            if self.is_consistent(var, value, assignment):
                # print("Variable %d: %d is consistent" % (var, value))
                assignment[var] = value
                # print("\033[92mConsistent\033[0m: %s added to assignment (%s)" % (value, assignment))
            
                # Save domains for if we need to roll back inferences
                domain_save = deepcopy(self.domains)
                # Preemptively set current domain to chosen value
                self.domains[var] = [value]
                inferences = self.ac_3()
                # print("\033[96mAC3: Domain reduced from\033[0m %s \033[96mto\033[0m %s" % (domain_save, self.domains))
                forward_assignments = [(var, self.domains[var][0]) for var in self.domains 
                                        if len(self.domains[var]) == 1 and var not in assignment]
                # print("Forward checking assignments: %s" % forward_assignments)

                # If inferences are valid, move on to try and assign the next variable
                if inferences:
                    # print("\033[96mAdding inferences to assignment:\033[0m %s" % forward_assignments)
                    self.add_assignments(forward_assignments, assignment)
                    result = self.back_track(assignment)
                    if result:
                        return result
                
                # Append current value assignment as well so it can be rolled back below
                forward_assignments.append((var, value))
                # print("Forward checking assignments backtracked: %s" % forward_assignments)
                # print("\033[96mResetting current domain from\033[0m %s \033[96mto\033[0m %s" % (self.domains, domain_save))
                
                # We have reached a dead end or inconsistency. Reset our domain and assignment to before value was set.
                self.domains = domain_save
                if inferences:
                    # print("Removing %s from assignment: %s" % (forward_assignments, assignment))
                    self.del_assignments(forward_assignments, assignment)
                    # print("Removal successful. New assignment: %s" % assignment)
        
        return False

    def add_assignments(self, forward_assignments: List[tuple], assignment: Dict[int, int]):
        """
        Adds assignments to assignment.

        Adds variable:value pairs in forward_assignment to assignment.

        Parameters
        ----------
        self : CSP
            Current CSP object
        forward_assignment : List[tuple]
            List of (variable, value) pairs to be added to assignment
        assignment : Dict[int, int]
            Assignment dictionary

        Returns
        -------
        None

        """
        for variable, value in forward_assignments:
            assignment[variable] = value

    def del_assignments(self, forward_assignments: List[tuple], assignment: Dict[int, int]):
        """
        Delete assignments from assignment.

        Deletes variable:value pairs in forward_assignment from assignment.

        Parameters
        ----------
        self : CSP
            Current CSP object
        forward_assignment : List[tuple]
            List of (variable, value) pairs to be deleted from assignment
        assignment : Dict[int, int]
            Assignment dictionary

        Returns
        -------
        None

        """
        for variable, _ in forward_assignments:
            del assignment[variable]

    def select_unassigned_var(self, assignment: Dict[int, int]):
        """
        Selects which variable to assign next.

        Uses Minimum Remaining Value Heuristic to find which variable to assign next. If there is a tie,
        uses Degree Heuristic on the remaining values.

        Parameters
        ----------
        self : CSP
            Current CSP object
        assignment : Dict[int, int]
            Assignment dictionary

        Returns
        -------
        int
            Variable chosen by MRV and Degree Heuristics

        """
        # print("MRV started...")
        
        # Process variable with Minimum Remaining Value (MRV) Heuristic
        domain_size = sys.maxsize
        for var in self.domains:
            # print("Evaluating domain size of %s" % var)
            if var not in assignment and len(self.domains[var]) < domain_size:
                domain_size = len(self.domains[var])

        # print("Minimum domain size is %s" % domain_size)
        
        tied_vars = [var for var in self.domains if var not in assignment and len(self.domains[var]) == domain_size]

        # Return variable and skip Degree Heuristic if only one variable remains
        if len(tied_vars) == 1:
            return tied_vars[0]

        # print("Degree H started...")
        # print("Variables with domains of size %s: %s" % (domain_size, tied_vars))

        # Process remaining variables with Degree Heuristic
        ret_var = tied_vars[0]
        max_constraints = 0
        for var in tied_vars:
            cur_constraints = 0
            for arc, _ in self.constraints[var]:
                if len(arc) == 2 and arc[1] not in assignment:
                    cur_constraints += 1

            # print("Number of constraints for variable %s: %s" % (var, cur_constraints))
            if cur_constraints > max_constraints:
                max_constraints = cur_constraints
                ret_var = var
        
        return ret_var

    def get_ordered_domain(self, variable: int):
        """
        Get ordered domain list.

        Use Least Constraining Value heuristic to return an ordered domain.

        Parameters
        ----------
        self : CSP
            Current CSP object
        variable : int
            Variable name/value used to find its domain

        Returns
        -------
        List[int]
            Ordered domain of variable

        """
        # "Least Constraining Value" heuristic
        ordered_domains = {}
        constraints = [(arc, constraint) for arc, constraint in self.constraints[variable] if len(arc) == 2]
        # Adds total number of values constrained in other domains for each value in domain of variable
        for value in self.domains[variable]:
            ordered_domains[value] = 0
            for arc, constraint in constraints:
                for arc_value in self.domains[arc[1]]:
                    if not constraint(value, arc_value):
                        ordered_domains[value] += 1

        # Returns ordered list of values
        return [var for var, _ in sorted(ordered_domains.items(), key=lambda item: item[1])]

    def is_consistent(self, variable: int, value: int, assignment: Dict[int, int]):
        """
        Check if current variable will be consistent with current assignment.

        Checks if variable/value will be consistent or satisfy all constraints with variables
        in assignment.

        Parameters
        ----------
        self : CSP
            Current CSP object
        variable : int
            Variable name/number
        value : int
            Value in Variable's domain being tested
        assignment : Dict[int, int]
            Assignment dictionary

        Returns
        -------
        boolean
            Returns true if value satisfies all constraints for values in assignment. Returns
            false otherwise.

        """
        assigned_variables = [(var, assignment[var]) for var in assignment if var != variable]
        for constraint in self.constraints[variable]:
            if constraint[0] == (variable, ) and not constraint[1](value):
                return False
            for assigned_var, assigned_val in assigned_variables:
                if constraint[0] == (variable, assigned_var) and not constraint[1](value, assigned_val):
                    return False

        return True

    def ac_3(self):
        """
        Perform ac-3 forward checking.

        Cycle through all arcs and call revise to edit variable domains until queue is empty.

        Parameters
        ----------
        self : CSP
            Current CSP object

        Returns
        -------
        boolean
            Returns false if domains result in an inconsistency or an empty domain. Returns
            true otherwise.

        """
        if self.forward_check:
            # print("AC3 ACTIVATED")
            queue = self.arcs[:]
            while queue:
                (x, y) = queue.pop(0)
                revised = self.revise(x, y)
                if not self.domains[x]:
                    return False
        
                if revised:
                    neighbors = [arc for arc in self.arcs if arc[1] == x]
                    queue = queue + neighbors

        return True

    def revise(self, x: int, y: int):
        """
        Edit domain of x based on domain of y.

        Delete all values in domain x in which there is no value in domain y
        that satisfies constraints between x -> y.

        Parameters
        ----------
        self : CSP
            Current CSP object
        x : int
            Variable whose domain is being scrubbed
        y : int
            Variable whose domain is being compared

        Returns
        -------
        boolean
            True if any value was removed from domain x. False otherwise.

        """
        revised = False

        # Domains
        x_dom = self.domains[x]
        y_dom = self.domains[y]

        # Get all constraints between x -> y
        constraints = [constraint[1] for constraint in self.constraints[x] if constraint[0] == (x, y)]
        # Safety check. Return false if no constraints
        if not constraints:
            return revised

        # print("\nCurrent arc: (%d, %d)" % (x, y))

        # Remove element from x domain if no value in y domain satisfies the constraints
        for X in x_dom[:]:
            # satisfied = False
            y_success = {var: 0 for var in y_dom}
            # print("Processing %d..." % X)
            for Y in y_dom:
                for constraint in constraints:
                    if constraint(X, Y):
                        y_success[Y] += 1

            if len(constraints) in y_success.values():
                break

            x_dom.remove(X)
            revised = True
                # for constraint in constraints:
                #     if constraint(X, Y):
                #         satisfied = True
                #         break
                # else:
                #     continue
                # break
            # if not satisfied:
            #     # print("No matches were found. Removing %d." % X)
            #     x_dom.remove(X)
            #     # print("%s's domain is now %s" % (X, self.domains[x]))
            #     revised = True
        
        return revised

    def print_assignment(self, assignment: Dict[int, int]):
        """
        Prints solution to CSP.

        Prints assignment values in order of its variable name/value in ascending order.

        Parameters
        ----------
        self : CSP
            Current CSP object
        assignment : Dict[int, int]
            Solution assignment to CSP

        Returns
        -------
        None
        """
        for x in self.variables:
            print(assignment[x])

    def __str__(self):
        """
        Summary line.

        Extended description of function.

        Parameters
        ----------
        arg1 : int
            Description of arg1

        Returns
        -------
        int
            Description of return value

        """
        arcs = []
        for var in self.constraints:
            for arc in self.constraints[var]:
                arcs.append(arc[0])

        return f"\nVariables: {self.variables}\nDomains: {self.domains}\nConstraints: {arcs}\nArcs: {self.arcs}"


def main():
    if len(sys.argv) != 3:
        print("\033[93m" + "Warning: csp_solver.py requires two arguments in the form of "
        + "\"python csp_solver.py [problem_filename] [use_forward_check_flag]\". \nExample: " 
        + "\"python csp_solver.py ./problem_files/problem_file_1.txt true\"" + "\033[0m")
        return

    V, D, C = process_file(sys.argv[1])
    forward_check = int(sys.argv[2])
    csp = CSP(V, D, C, forward_check)

    # csp.get_ordered_domain(1, {})
    # print(csp)
    # csp.ac_3()
    # print(csp)

    # assignment = {0:1}
    # print(csp.select_unassigned_var(assignment))

    # start = time.time()
    assignment = csp.back_track()
    # print("\n\033[92mFinal Assignment:\033[0m %s" % assignment)
    csp.print_assignment(assignment)
    # print("Backtrack ran for: %s" % str(time.time() - start))
    # print("Backtrack was called: %s" % csp.calls_to_backtrack)

def process_file(file):
    """
    Reads in file into a list.

    Delimits domain line into first row of list and subsequent lines
    will be filled with constraints.

    Parameters
    ----------
    file : str
        Problem file name

    Returns
    -------
    tuple
        Tuple containing Variable Dict, Domain Dict, and Constraint Dict
        created in make_CSP_coponents.

    """
    f = open(file, "r")
    split_lines = []

    line = f.readline()
    split_lines.append(line.strip().split(":"))

    for line in f:
        split_lines.append(line.split())

    return make_CSP_components(split_lines)

def make_CSP_components(lines: list):
    """
    Construct Variable, Domain, and Constraint lists.

    Uses read in lines to construct three dictoinaries that house the variable names, 
    domains, and constraints for each variable.

    Parameters
    ----------
    lines : list
        Lines from problem file delimited into a list.

    Returns
    -------
    tuple
        Tuple containing Variable Dict, Domain Dict, and Constraint Dict

    """
    # Get number of variables
    num_vars = 0
    for i in range(1, len(lines)):
        if int(lines[i][2][1:]) > num_vars:
            num_vars = int(lines[i][2][1:])
        if lines[i][6][0] == 'X' and int(lines[i][6][1:]) > num_vars:
            num_vars = int(lines[i][6][1:])
    
    # Variable list i.e. [0, 1, 2, ...]
    V = [i for i in range(num_vars + 1)]

    # Make list of domains
    D_list = [[i for i in range(int(lines[0][j]))] for j in range(len(lines[0]))]
    while len(D_list) != len(V):
        D_list.append(D_list[-1])

    # Domain list i.e. {0: [0, 1, 2, ...], 1: [0, 1, 2, ...], ...}
    D = {}
    for i in range(len(V)):
        D[V[i]] = list(D_list[i])
    
    # Constraint list i.e. {0: [((0, 1), lambda function), ...], ...}
    C = {}
    for i in V:
        C[i] = []

    for i in range(1, len(lines)):
        line = lines[i]
        make_constraints(line, C)

    return V, D, C

def make_constraints(constraint: list, C: Dict[int, list]):
    """
    Helper function that formats a constraint.

    Appends a constraint of the form ((x, y), constraint(x, y)) to the constraint
    dictionary.

    Parameters
    ----------
    constraint : list
        List containing constraint components (i.e. [int, *, var, +, int, rel, var/int])

    C: Dict[int, list]
        Dictionary used to store constraints

    Returns
    -------
    None

    """
    # Comparison operators
    comp_ops = {
        "==": (int.__eq__, int.__eq__),
        "!=": (int.__ne__, int.__ne__),
        "<=": (int.__le__, int.__ge__),
        ">=": (int.__ge__, int.__le__),
        "<": (int.__lt__, int.__gt__),
        ">": (int.__gt__, int.__lt__)
    }

    # Construct binary constraint
    if constraint[6][0] == 'X':
        var1, var2, int1, int2, comp = int(constraint[2][1:]), int(constraint[6][1:]), int(constraint[0]), int(constraint[4]), comp_ops[constraint[5]]
        C[var1].append(((var1, var2), lambda x, y: comp[0](int1 * x + int2, y)))
        C[var2].append(((var2, var1), lambda x, y: comp[1](x, int1* y + int2)))
    # Construct unary constraint
    else:
        var1, int1, int2, int3, comp = int(constraint[2][1:]), int(constraint[0]), int(constraint[4]), int(constraint[6]), comp_ops[constraint[5]]
        C[var1].append(((var1, ), lambda x: comp[0](int1 * x + int2, int3)))

if __name__ == "__main__":
    main()
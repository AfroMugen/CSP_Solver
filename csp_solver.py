from copy import deepcopy
import sys
from typing import List, Dict
from itertools import permutations

class CSP():
    def __init__(self, variables: list, domains: Dict[int, List], constraints: Dict[int, List], forward_check: bool):
        self.variables = variables
        self.domains = domains
        self.constraints = constraints
        self.arcs = self.get_arcs()
        self.forward_check = forward_check

    def get_arcs(self):
        arcs = []
        for variable in self.constraints:
            for constraint in self.constraints[variable]:
                if len(constraint[0]) == 2:
                    arcs.append(constraint[0])

        return arcs

    def back_track(self, assignment: dict = {}):
        print("\n\033[91mCurrent assignment:\033[0m %s" % assignment)
        if len(assignment) == len(self.variables):
            return assignment

        # To be changed to "Most Restricted Variable" and "Degree" heuristics
        var = [var for var in self.variables if var not in assignment][0]
        print("\033[93mProcessing variable:\033[0m %s" % var)
        for value in self.get_ordered_domain(var, assignment):
            print("Trying value: %s..." % value)
            if self.is_consistent(var, value, assignment):
                # print("Variable %d: %d is consistent" % (var, value))
                assignment[var] = value
                print("\033[92mConsistent\033[0m: %s added to assignment (%s)" % (value, assignment))

            
            domain_save = deepcopy(self.domains)
            # Preemptively set current domain to chosen value
            self.domains[var] = [value]
            inferences = self.ac_3()
            print("\033[96mAC3: Domain reduced from\033[0m %s \033[96mto\033[0m %s" % (domain_save, self.domains))
            forward_assignments = [(var, self.domains[var][0]) for var in self.domains 
                                    if len(self.domains[var]) == 1 and var not in assignment]
            if inferences:
                print("\033[96mAdding inferences to assignment:\033[0m %s" % forward_assignments)
                self.add_assignments(forward_assignments, assignment)
                result = self.back_track(assignment)
                if result:
                    return result
            
            print("\033[96mResetting current domain from\033[0m %s \033[96mto\033[0m %s" % (self.domains, domain_save))
            # We have reached a dead end or inconsistency. Reset our domain and assignment to before value was set.
            self.domains = domain_save
            if inferences:
                print("Removing %s from assignment: %s" % (forward_assignments.append((var, value)), assignment))
                self.del_assignments(forward_assignments.append((var, value)), assignment)
                print("Removal successful. New assignment: %s" % assignment)
        
        return False

    def add_assignments(self, forward_assignments: List[tuple], assignment: Dict[int, int]):
        for variable, value in forward_assignments:
            assignment[variable] = value

    def del_assignments(self, forward_assignments: List[tuple], assignment: Dict[int, int]):
        for variable, _ in forward_assignments:
            del assignment[variable]

    def get_ordered_domain(self, variable: int, assignment: Dict[int, int]):
        # To be changed to "Least Constraining Value" heuristic
        return self.domains[variable]

    def is_consistent(self, variable: int, value: int, assignment: Dict[int, int]):
        assigned_variables = [(var, assignment[var]) for var in assignment if var != variable]
        for constraint in self.constraints[variable]:
            if constraint[0] == (variable, ) and not constraint[1](value):
                return False
            for assigned_var, assigned_val in assigned_variables:
                if constraint[0] == (variable, assigned_var) and not constraint[1](value, assigned_val):
                    return False

        return True

    def ac_3(self):
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
        revised = False

        x_dom = self.domains[x]
        y_dom = self.domains[y]

        constraints = [constraint[1] for constraint in self.constraints[x] if constraint[0] == (x, y)]
        # constraint_debug = [constraint for constraint in self.constraints[x] if constraint[0] == (x, y)]
        # print(constraint_debug)
        if not constraints:
            return revised
        # print("\nCurrent arc: (%d, %d)" % (x, y))
        for X in x_dom[:]:
            satisfied = False
            # print("Processing %d..." % X)
            for Y in y_dom:
                for constraint in constraints:
                    if constraint(X, Y):
                        satisfied = True
                        break
                else:
                    continue
                break
            if not satisfied:
                # print("No matches were found. Removing %d." % X)
                x_dom.remove(X)
                # print("%s's domain is now %s" % (X, self.domains[x]))
                revised = True
        
        return revised

    def __str__(self):
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
    forward_check = sys.argv[2]
    csp = CSP(V, D, C, forward_check)
    # print(csp)
    # csp.ac_3()
    # print(csp)
    assignment = csp.back_track()
    print("\n\033[92mFinal Assignment:\033[0m %s" % assignment)

def process_file(file):
    f = open(file, "r")
    split_lines = []

    line = f.readline()
    split_lines.append(line.strip().split(":"))

    for line in f:
        split_lines.append(line.split())

    return make_CSP_components(split_lines)

def make_CSP_components(lines: list):
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
        
    # print(V)
    # print(D)
    # print(C)
    # for var in C:
    #     for constraint in C[var]:
    #         if len(constraint[0]) > 1:
    #             print(constraint[1](1, 1))
    #         else:
    #             print(constraint[1](1))

    return V, D, C

def make_constraints(constraint: str, C: Dict[int, list]):
    # Comparison operators
    comp_ops = {
        "==": (int.__eq__, int.__eq__),
        "!=": (int.__ne__, int.__ne__),
        "<=": (int.__le__, int.__ge__),
        ">=": (int.__ge__, int.__le__),
        "<": (int.__lt__, int.__gt__),
        ">": (int.__gt__, int.__lt__)
    }

    if constraint[6][0] == 'X':
        var1, var2, int1, int2, comp = int(constraint[2][1:]), int(constraint[6][1:]), int(constraint[0]), int(constraint[4]), comp_ops[constraint[5]]
        C[var1].append(((var1, var2), lambda x, y: comp[0](int1 * x + int2, y)))
        C[var2].append(((var2, var1), lambda x, y: comp[1](x, int1* y + int2)))
        # C[var1].append(((var1, var2), lambda x, y: print("%s * %s + %s %s %s is %s" % (int1, x, int2, constraint[5], y, comp[0](int1 * x + int2, y)))))
        # C[var2].append(((var2, var1), lambda x, y: print("%s * %s + %s %s %s is %s" % (int1, y, int2, constraint[5], x, comp[1](x, int1* y + int2)))))
    else:
        var1, int1, int2, int3, comp = int(constraint[2][1:]), int(constraint[0]), int(constraint[4]), int(constraint[6]), comp_ops[constraint[5]]
        C[var1].append(((var1, ), lambda x: comp[0](int1 * x + int2, int3)))
        # C[var1].append(((var1, ), lambda x: print("%s * %s + %s %s %s is %s" % (int1, var1, int2, constraint[5], int3, comp[0](int1 * x + int2, int3)))))


if __name__ == "__main__":
    main()
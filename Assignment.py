import copy
import itertools
from threading import Thread


class CSP:
    def __init__(self):
        # self.variables is a list of the variable names in the CSP
        self.variables = []

        # self.domains[i] is a list of legal values for variable i
        self.domains = {}

        # self.constraints[i][j] is a list of legal value pairs for
        # the variable pair (i, j)
        self.constraints = {}
        self.backtrack_count = 0
        self.backtrack_fails = 0

    def add_variable(self, name, domain):
        """Add a new variable to the CSP. 'name' is the variable name
        and 'domain' is a list of the legal values for the variable.
        """
        self.variables.append(name)
        self.domains[name] = list(domain)
        self.constraints[name] = {}


    def get_all_possible_pairs(self, a, b):
        """Get a list of all possible pairs (as tuples) of the values in
        the lists 'a' and 'b', where the first component comes from list
        'a' and the second component comes from list 'b'.
        """
        return itertools.product(a, b)

    def get_all_arcs(self):
        """Get a list of all arcs/constraints that have been defined in
        the CSP. The arcs/constraints are represented as tuples (i, j),
        indicating a constraint between variable 'i' and 'j'.
        """
        return [(i, j) for i in self.constraints for j in self.constraints[i]]

    def get_all_neighboring_arcs(self, var):
        """Get a list of all arcs/constraints going to/from variable
        'var'. The arcs/constraints are represented as in get_all_arcs().
        """
        return [(i, var) for i in self.constraints[var]]

    def add_constraint_one_way(self, i, j, filter_function):
        """Add a new constraint between variables 'i' and 'j'. The legal
        values are specified by supplying a function 'filter_function',
        that returns True for legal value pairs and False for illegal
        value pairs. This function only adds the constraint one way,
        from i -> j. You must ensure that the function also gets called
        to add the constraint the other way, j -> i, as all constraints
        are supposed to be two-way connections!
        """
        if not j in self.constraints[i]:
            # First, get a list of all possible pairs of values between variables i and j
            self.constraints[i][j] = self.get_all_possible_pairs(self.domains[i], self.domains[j])

        # Next, filter this list of value pairs through the function
        # 'filter_function', so that only the legal value pairs remain
        self.constraints[i][j] = filter(lambda value_pair: filter_function(*value_pair), self.constraints[i][j])

    def add_all_different_constraint(self, variables):
        """Add an Alldiff constraint between all of the variables in the
        list 'variables'.
        """
        for (i, j) in self.get_all_possible_pairs(variables, variables):
            if i != j:
                self.add_constraint_one_way(i, j, lambda x, y: x != y)

    def backtracking_search(self):
        """This functions starts the CSP solver and returns the found
        solution.
        """

        assignment = copy.deepcopy(self.domains)
        self.inference(assignment, self.get_all_arcs())
        self.backtrack_count += 1
        return self.backtrack(assignment)

    def select_unassigned_variable(self, assignment):       # We want to choose the variable with the least possible domain options (more than 1 though)
        least = 10
        for variable, variabledomain in assignment.items():
            l = len(variabledomain)
            if l < least and l > 1:     # We just find the variable with the shortest domain list larger than one
                unassigned = variable
        return unassigned

    def assignmentIsComplete(self, assignment): # TODO: effektiviser
            for value in assignment.values():
                if len(value) > 1:
                    return False
            return True

    def backtrack(self, assignment):    #  Recursively tries domain values until it finds the ones that works

        if self.assignmentIsComplete(assignment):   # If we have found a solution for all domains
            return assignment


        unassignedVar = self.select_unassigned_variable(assignment) # chooses some unassigned variable

        for value in assignment[unassignedVar]:                     # goes through each value in its domain, and we want to see if it can solve our problem
            self.backtrack_count += 1                               # just to see how many times we call backtrack
            newAssignment = copy.deepcopy(assignment)               # new domain state (we make a new deep copy for each value so that the recursive calls don't influence each other when one fails)
            newAssignment[unassignedVar] = [value]
            if self.inference(newAssignment, self.get_all_arcs()):  # TODO: get_all_arcs(newAssignment)? mulig vi ikke trenger å gå gjennom alle hele tiden...
                result = self.backtrack(newAssignment)
                if result:
                    return result                                   # Eventually we will reach a value assignment s.t. all variables have a value, and return this. this is our solution
        self.backtrack_fails += 1
        return False  # here the path we started to take led to a variable not being bound, and so we return the empty domain to show it's not a solution


    def inference(self, assignment, queue):     # returns false if revise removed all domain values from a variable, because the path we're currently on will then be wrong

        while queue:	                        # as long as there still are elements to go through
            x, y = queue.pop(0)                 # Destructure elements in queue as elements x and y (basically, x='i1-j1', y='i2-j2')
            if self.revise(assignment, x, y):   # If we have revised something (removed possible values from the domains of the variables)
                if not assignment[x]:           # and possible values for x is now 0, we've done something wrong, and we need to backtrack
                    self.backtrack_fails += 1
                    return False
                for neighbour in self.get_all_neighboring_arcs(x):  # else we add every neighbour of x to the queue unless it is y
                    if neighbour[0] != y:
                        queue.append((neighbour[0], x))
        return True


    def revise(self, assignment, i, j):  # Revise checks if there are any inconsistencies with the constraints, and removes them if that is the case

        revised = False

        for xi in assignment[i]:	        # assignment[i] gives a list for variable i, e.g. assignment["1-1"] => [1,2,3,4,5,6,7,8,9]. So for each value in this list, do:
            noSatisfaction = True			            # whether we should delete an xi or not
            for xj in assignment[j]:	                # we also go through each value xj in assignment of j
                if (xi, xj) in self.constraints[i][j]:	# If the tuple is in the constraints, we don't want to delete it as it is a possible assignment of values for the variables i and j
                    noSatisfaction = False
            if noSatisfaction:                      # if we didn't find it in constraints, we want to remove xi from the domain of i
                assignment[i].remove(xi)
                revised = True                      # Revised is true because we have changed something
        return revised


def create_sudoku_csp(filename):
    """Instantiate a CSP representing the Sudoku board found in the text
    file named 'filename' in the current directory.
    """
    csp = CSP()
    board = list(map(lambda x: x.strip(), open(filename, 'r')))

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                csp.add_variable('%d-%d' % (row, col), list(map(str, range(1, 10)))) # tall fra 1-9 er mulige til vi utelukker dem
            else:
                csp.add_variable('%d-%d' % (row, col), [board[row][col]]) # nytt listeelement med verdien

    # X blir en liste med hvert element i sudokutabellen, "i-j"
    # Domains får nytt entry slik at "i-j" => [1-9], med mindre det står et tall i ruta, da blir "i-j" => tall
    # Constraints blir slik at "i-j" => {}  en tom dict

    for row in range(9):
        csp.add_all_different_constraint(['%d-%d' % (row, col) for col in range(9)])
    for col in range(9):
        csp.add_all_different_constraint(['%d-%d' % (row, col) for row in range(9)])
    for box_row in range(3):
        for box_col in range(3):
            cells = []
            for row in range(box_row * 3, (box_row + 1) * 3):
                for col in range(box_col * 3, (box_col + 1) * 3):
                    cells.append('%d-%d' % (row, col))
            csp.add_all_different_constraint(cells)

    # Oppdaterer basic constraints for rad, kolonne og firkant med 9 tall slik at

    for constraint in csp.constraints:
        for entry in csp.constraints[constraint]:
            csp.constraints[constraint][entry] = list(csp.constraints[constraint][entry])
    return csp


def print_sudoku_solution(solution):
    """Convert the representation of a Sudoku solution as returned from
    the method CSP.backtracking_search(), into a human readable
    representation.
    """
    for row in range(9):
        for col in range(9):
            print(solution['%d-%d' % (row, col)][0], end=" "),
            if col == 2 or col == 5:
                print('|', end=" "),
        print("")
        if row == 2 or row == 5:
            print('------+-------+------')

def isLegal(board):
    for row in range(0,9):
        values = [0 for i in range(0,9)]
        for col in range(0,9):
            var = '%d-%d' % (row, col)
            values[board[var][0]] = 1
        if 0 in values:
            return False
    for col in range(0,9):
        values = [0 for i in range(0,9)]
        for row in range(0,9):
            var = '%d-%d' % (row, col)
            values[board[var][0]] = 1
        if 0 in values:
            return False

filenames = ["easy.txt", "medium.txt", "hard.txt", "veryhard.txt", "extremelyhard.txt"]

def run(fileno):
    print(" ____SOLUTION OF %s ____" % filenames[fileno] )
    csp = create_sudoku_csp(filenames[fileno])
    solution = csp.backtracking_search()
    print_sudoku_solution(solution)
    print("backtrack calls: ", csp.backtrack_count)
    print("backtrack fails: ", csp.backtrack_fails)

run(0)
run(1)
run(2)
run(3)
run(4)

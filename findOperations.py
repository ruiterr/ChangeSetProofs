# -*- coding: utf-8 -*-
import numpy as np

allOperations = {}

class Op:
    def __init__(self, name, inverse, paramNames, paramValues = None):
        
        self.paramNames = paramNames
        self.paramValues = paramValues if paramValues != None else [0 for x in paramNames]
        

        self.name = name 
        self.inverse = inverse

        allOperations[self.getRegistrationName(self.name, self.paramNames, self.paramValues)] = self
        
    def inv(self):
        inverseName = self.getRegistrationName(self.inverse, self.paramNames, self.paramValues)
        if inverseName in allOperations:
            return allOperations[inverseName]
        
        inverseOp = Op(self.inverse, self.name, self.paramNames, self.paramValues)
        return inverseOp
    
    def __str__(self):
        return self.getRegistrationName(self.name, self.paramNames, self.paramValues)
    
    def getRegistrationName(self, base, paramNames, paramValues):
        registrationName = base
        
        for name, value in zip(paramNames, paramValues):
            if type(value) == int:
                if value > 0:
                    registrationName += '_' + name + '+' + str(value)
                if value < 0:
                    registrationName += '_' + name  + str(value)
            if type(value) == str:
                registrationName += '_' + str(value)
            if type(value) == list:
                if (len(value) > 0):
                    registrationName += '_' + name + '=' + "".join(value)
        
        return registrationName
    
    def modifyParam(self, name, value, op="push"):
        newParamValues = list(self.paramValues)
        paramIndex = self.paramNames.index(name)
        
        if type(newParamValues[paramIndex]) == int:
            newParamValues[paramIndex] += value
        elif type(newParamValues[paramIndex]) == str:
            newParamValues[paramIndex] = value
        elif type(newParamValues[paramIndex]) == list:
            newParamValues[paramIndex] = list(newParamValues[paramIndex])
            if op == "push":
                newParamValues[paramIndex].append(value)
                newParamValues[paramIndex].sort()
            if op == "pop":
                newParamValues[paramIndex].pop()
            if op == "remove":
                newParamValues[paramIndex].remove(value)
        
        return self.getFromParams(newParamValues)
    
    def getParam(self, name):
        paramIndex = self.paramNames.index(name)
        return self.paramValues[paramIndex]
    
    def getFromParams(self, newParamValues):
        newOpName = self.getRegistrationName(self.name, self.paramNames, newParamValues)
        
        if newOpName in allOperations:
            return allOperations[newOpName]
        
        newOp = Op(self.name, self.inverse, self.paramNames, newParamValues)
        return newOp
    
def findOpFromBandC(grid, B, C):
    if B == None:
        return None
    if C == None:
        return None
    
    if not B in grid:
        return None
    
    A = None
    for op in grid.keys():
        if grid[op][B] == C:
            A = op
            
    return A

def rebase(grid, A, B):
    if A== None: return None
    if B== None: return None
    
    if not A in grid:
        return None
    if not B in grid[A]:
        return None
    
    return grid[A][B]

def createRule(grid, RuleConstructor, A, B, C, inputs, invalidCase=False):
    if A == None or B == None or C==None:
        return None
    
    if grid!= None:
        if (not A in grid) or (not B in grid):
            #print("Failed %s %s" % (A, B))
            return None
    
    return RuleConstructor(A, B, C, inputs, invalidCase)

def inv(A):
    if A == None:
        return None
    
    return A.inv()

def getOpListFromGrid(grid):
    OpList = grid.keys()
    
    return [(i, j, grid[i][j]) for i in OpList for j in OpList if grid[i][j] != None]

class Rule:
    def __init__(self, A, B, C, inputs, invalidCase = False):
        self.A = A
        self.B = B
        self.C = C
        self.inputs = inputs
        self.invalid = invalidCase
    

    @staticmethod 
    def getNumInputs():
        return 0
    
    @staticmethod 
    def apply(grid, operations):
        return None
    
    def str(self):
        return self.__class__.__name__ + ' ' + str(self.A) + ' ↷ ' + str(self.B) + ' = ' + str(self.C) + '(' + ",".join([str(X) for X in self.inputs]) + ')'

class Rule1(Rule):
    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        U = rebase(grid, A, B)
        
        
        return createRule(grid, Rule1, U, inv(B), A, operations)

class Rule2(Rule):

    @staticmethod 
    def getNumInputs():
        return 1
    
    @staticmethod 
    def apply(grid, operations):
        A = operations[0]
        Z = rebase(grid, A, A)
        
        
        return createRule(grid, Rule2, inv(A), Z, inv(Z), operations)

class Rule3(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        U = rebase(grid, inv(A), inv(A))
        V = rebase(grid, U, B)
        W = rebase(grid, A, B)
        
        return createRule(grid, Rule3, V, W, inv(W), operations)

class Rule4(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        U = rebase(grid, A, B)
        V = rebase(grid, inv(A), inv(A))
        W = findOpFromBandC(grid, U, inv(U))
        
        return createRule(grid, Rule4, V, B, W, operations)

class Rule5(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        X = findOpFromBandC(grid, B, A)
        
        return createRule(grid, Rule5, A, inv(B), X, operations)

class Rule6(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        
        T = rebase(grid, A, A)
        U = rebase(grid, T, B)
        V = rebase(grid, inv(A), B)
                
        return createRule(grid, Rule6, V, U, inv(U), operations)

class InsertRule(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        
        if B.name != 'I':
            return None
        
        i_A = A.getParam('i')
        p_A = A.getParam('p')
        s_A = A.getParam('s')
        c_A = A.getParam('c')
        e_A = A.getParam('e')
        i_B = B.getParam('i')
        p_B = B.getParam('p')
        s_B = B.getParam('s')
        c_B = B.getParam('c')
        e_B = B.getParam('e')

        #if str(inv(B)) in e_A:
            #print ("Canceling error")
        #    return createRule(grid, InsertRule, A, B, A.modifyParam('e', str(inv(B)),'remove'), operations)

        # Invalid operations are ignored in rebases
        #if len(e_B) > 0:
        #    return createRule(grid, RemoveRule, A, B, A, operations)

        # broken operations do get extended with all rebased operations
        #if len(e_A) > 0:
        #    return createRule(grid, RemoveRule, A, B, A.modifyParam('e', str(B), 'push'), operations)

        if i_A == i_B and (p_A != p_B):
        #    return None
            return createRule(grid, RemoveRule, A, B, A, operations, True)
        if i_B in s_A and p_A != p_B and c_B == 0 and i_A != i_B:
            return createRule(grid, InsertRule, A, B, A, operations, True)

        #if i_B in s_A and p_A != p_B:
        #    # Non matching scaffolding encountered
        #    return createRule(grid, InsertRule, A, B, A.modifyParam('e', str(B), 'push'), operations)

        #if i_A == i_B and (len(s_A) != 0 or len(s_B) != 0):
        #    return None
        #if i_A == i_B and (c_A != 0 or c_B != 0):
        #    return None
        #if c_A != 0 or c_B != 0:
        #    return None
        #if len(s_B) != 0:
        #if len(s_B) != 0:
        #    return None

        #if i_B in s_A and p_A != p_B:
            # Keep unchanged
            #return createRule(grid, InsertRule, A, B, A, operations)
            #return createRule(grid, InsertRule, A, B, A.modifyParam('s', i_B, 'remove'), operations)
        #    return None
        #if p_A != p_B:
        #    return None

        if p_A > p_B:
            #  Is this a canceled operation?
            if c_B != 0:
                # Canceled operations don't affect the scaffolding
                return createRule(grid, InsertRule, A, B, A, operations)
            else:
                # All operations at a higher position are just shifted
                return createRule(grid, InsertRule, A, B, A.modifyParam('p', 1), operations)
        elif p_A < p_B:
            # Operations at a lower position remain unchanged
            return createRule(grid, InsertRule, A, B, A, operations)
        else:
            # If operations are at the same position, we have to distinguish
            # whether they are the same operation (based on their ID)
            if i_A == i_B:
                # If this is the same operation, we have to increase the cancelation counter
                return createRule(grid, InsertRule, A, B, A.modifyParam('c', 1), operations)
            else:    
                # These are different operations. Is this a canceled operation?
                if c_B != 0:
                    # Canceled operations don't affect the scaffolding
                    return createRule(grid, InsertRule, A, B, A, operations)
                else:
                    if i_B in s_A:
                        # Remove the scaffolding entry, but keep position
                        return createRule(grid, InsertRule, A, B, A.modifyParam('s', i_B, 'remove'), operations)
                    else:
                        # No scaffolding, so we shift position by one
                        return createRule(grid, InsertRule, A, B, A.modifyParam('p', 1), operations)

        return None
foundValues = set()

class RemoveRule(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        
        if B.name != 'R':
            return None
        
        i_A = A.getParam('i')
        p_A = A.getParam('p')
        s_A = A.getParam('s')
        c_A = A.getParam('c')
        e_A = A.getParam('e')
        i_B = B.getParam('i')
        p_B = B.getParam('p')
        s_B = B.getParam('s')
        c_B = B.getParam('c')
        e_B = B.getParam('e')
        
        #if i_A == i_B and (len(s_A) != 0 or len(s_B) != 0):
        #    return None
        if i_A == i_B and (p_A != p_B):
            #return None
            return createRule(grid, RemoveRule, A, B, A, operations, True)

        if i_B in s_A and p_A != p_B and c_B == 0 and i_A != i_B:
            return createRule(grid, InsertRule, A, B, A, operations, True)

       #     return createRule(grid, RemoveRule, A, B, A.modifyParam('e2', str(p_B), 'push'), operations)
       #     return None
        #if c_A != 0 or c_B != 0:
        #    return None
        #if len(s_B) != 0:
        #    return None
        #if str(inv(B)) in e_A:
        #    #print ("Canceling error")
        #    return createRule(grid, InsertRule, A, B, A.modifyParam('e', str(inv(B)),'remove'), operations)

        # Invalid operations are ignored in rebases
        #if len(e_B) > 0:
        #    return createRule(grid, RemoveRule, A, B, A, operations)

        # broken operations do get extended with all rebased operations
        #if len(e_A) > 0:
        #    return createRule(grid, RemoveRule, A, B, A.modifyParam('e', str(B), 'push'), operations)

        #if i_A == i_B and (p_A != p_B):
        #    return createRule(grid, RemoveRule, A, B, A.modifyParam('e', str(B), 'push'), operations)


        #if i_B in s_A and p_A == p_B+1 and c_A == 0 and c_B == 0 and i_A != i_B and len(s_B) == 0 and len(s_A) == 1:
            #return createRule(grid, RemoveRule, A, B, A.modifyParam('e', str(B), 'push'), operations)
            #return createRule(grid, RemoveRule, A, B, A.modifyParam('c', -1), operations)

        #    return None
            
        #if i_B in s_A and p_A != p_B:
        #    return None
            #opIndex = 0 if i_B == 'i' else 1

            #newValue = 10 * opIndex + p_B
            #foundValues.add(str(B))
            
            #return createRule(grid, RemoveRule, A, B, A.modifyParam('e', str(B), 'push'), operations)
            # Keep unchanged
            #return createRule(grid, InsertRule, A, B, A, operations)
            #return createRule(grid, RemoveRule, A, B, A.modifyParam('s', i_B, 'push'), operations)
        #if p_A != p_B:
        #    return None
        
        if p_A > p_B:
            #  Is this a canceled operation?
            if c_B != 0:
                # Canceled operations don't affect the scaffolding
                return createRule(grid, RemoveRule, A, B, A, operations)
            else:
                # All operations at a higher position are just shifted
                return createRule(grid, RemoveRule, A, B, A.modifyParam('p', -1), operations)
        elif p_A < p_B:
            # Operations at a lower position remain unchanged
            return createRule(grid, RemoveRule, A, B, A, operations)
        else:
            # If operations are at the same position, we have to distinguish
            # whether they are the same operation (based on their ID)
            if i_A == i_B:
                # If this is the same operation, we have to decrease the cancelation counter
                return createRule(grid, RemoveRule, A, B, A.modifyParam('c', -1), operations)
            else:    
                # These are different operations. Is this a canceled operation?
                if c_B != 0:
                    # Canceled operations don't affect the scaffolding
                    return createRule(grid, RemoveRule, A, B, A, operations)
                else:
                    # We add the ID to the scaffolding
                    return createRule(grid, RemoveRule, A, B, A.modifyParam('s', i_B, 'push'), operations)

class ShiftRightRule(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        
        C = rebase(grid, A, B)
        
        if C != None:
            return createRule(grid, ShiftRightRule, A.modifyParam('p', 1), B.modifyParam('p', 1), C.modifyParam('p', 1), operations)

rules = [Rule1, Rule2, Rule3, Rule4, Rule5, Rule6, InsertRule, RemoveRule]
# rules = [Rule1, Rule2, Rule3, Rule4, Rule5, Rule6, InsertRule, RemoveRule]
#rules = [Rule1, InsertRule, RemoveRule]
#rules = [Rule1, Rule3, InsertRule, RemoveRule]
#rules = [InsertRule, RemoveRule]
#rules = [Rule1, Rule2, Rule3, Rule4, Rule5, Rule6, ShiftRightRule]
#rules = [Rule1, Rule3]
def findOperations(operations, knownEntries, rules):
    grid = {}
    for op in operations:
        grid[op] = {}
        for op2 in operations:
            grid[op][op2] = None
    
    for entry in knownEntries:
        grid[entry[0]][entry[1]] = entry[2]
    
    def getAllTuples(l):
        if l==0:
            yield ()
        else:
            for op in operations:
                for L in getAllTuples(l-1):
                    yield (op,) + L
    
    appliedRules = []
    newEntryFound = True
    while newEntryFound:
        newEntryFound = False
        for r in rules:
            for ops in getAllTuples(r.getNumInputs()):
                result = r.apply(grid, ops)
                
                if result != None:
                    #print("Rule %s" %(result))
                    currentEntry = grid[result.A][result.B]
                    
                    if currentEntry == result.C:
                        continue
                    if currentEntry == None:
                        if result.A in grid and result.B in grid[result.A]:
                            grid[result.A][result.B] = result.C
                            newEntryFound = True
                            appliedRules.append(result)
                        else:
                            print("Entry Not Found")
                        continue
                    if currentEntry != result.C:
                        #print(len(ops))
                        print("Collision found for rule %s (input %s) operations: %s %s. Existing entry %s new Entry %s" % (r, ",".join([str(X) for X in ops]), result.A, result.B, currentEntry, result.C))
                        #return None
                    
    return (grid, appliedRules)

def gridToArray(grid):
    gridKeys = list(grid.keys())
    arr = []
    
    arr.append([""])
    for i in range(len(gridKeys)):
        arr[0].append('*' + str(gridKeys[i]) + '*')
        
    for i in range(len(gridKeys)):
        arr.append([])
        arr[i+1].append('*' + str(gridKeys[i]) + '*')
        for j in range(len(gridKeys)):
            value = grid[gridKeys[j]][gridKeys[i]]
            
            if value == None:
                arr[i+1].append("")
            else:
                arr[i+1].append(str(value))
    
    return np.array(arr)

bestFoundGrid = None
entriesInBestGrid = 0
def backtrackingSearch(operations, extraOps, knownEntries, rules, solutionsToFind):
    #print(len(knownEntries))
    # perform initial search of the grid
    result = findOperations(operations, knownEntries, rules)
    if result == None:
        return []
    
    grid, rules = result

    # check if there are still None entries in the grid
    NoneFound = False
    count = 0
    for A in operations:
        for B in operations:
            if grid[A][B] == None:
                NoneFound = True
            else:
                count = count + 1
    
    global entriesInBestGrid
    global bestFoundGrid
    print("Count: ", count)
    if count > entriesInBestGrid:
        entriesInBestGrid = count
        bestFoundGrid = (grid, rules, knownEntries)
        
    if not NoneFound:
        return [(grid, rules)]
    
    # The grid is not yet full, so we search the row with the largest number
    # of entries
    entriesPerRow = [len([X for X in operations if grid[X][Y] != None]) for Y in operations]
    entriesPerRow = [ (X if X < len(operations) else -1) for X in entriesPerRow];
    #ops = gridToArray(grid)
    #print(ops)
    #print(entriesPerRow)
    
    # Find the entry we want to try
    i = operations[np.asarray(entriesPerRow).argmax()]
    j = [X for X in operations if grid[X][i] == None][0]
    
    # Determine the set of values we have to try
    opsToTry = set(operations + extraOps) - set([grid[X][i] for X in operations if grid[X][i] == None])

    #print(j,i, [str(x) for x in opsToTry])
    solutions = []
    for op in opsToTry:
        newKnownEntries = knownEntries + [(j, i, op)]
        newSolutions = backtrackingSearch(operations, extraOps, newKnownEntries, rules, solutionsToFind - len(solutions))
        solutions = solutions + newSolutions
        if len(solutions) >= solutionsToFind:
            return solutions
    
    return solutions
    
#%% Define Operations
class O:
    I = Op('I', 'R', ['i', 'p', 's', 'c', 'e','e2'], ["i", 0, [], 0, [], []])
    R = I.inv()


for i in ["i", "j"]:
    I1 = O.I.modifyParam('i', i)
    R1 = O.R.modifyParam('i', i)
    for p in [-1, 0, 1]:
        I2 = I1.modifyParam('p', p)
        R2 = R1.modifyParam('p', p)
        for s in [[], ["i"], ["j"], ["i","j"], ["i","i"], ["j","j"]]:
            I3 = I2
            R3 = R2
            for value in s:
                I3 = I3.modifyParam('s', value, "push")
                R3 = R3.modifyParam('s', value, "push")

            for c in [-1, 0, 1]:
                I4 = I3.modifyParam('c', c)
                R4 = R3.modifyParam('c', c)
                
                for e in [[]]:
                    I5 = I4
                    R5 = R4
                    for value in e:
                        I5 = I5.modifyParam('e', value, "push")
                        R5 = R5.modifyParam('e', value, "push")
                    
                    setattr(O, str(I5), I5)
                    setattr(O, str(R5), R5)
                        #for e2 in [[], ["0"], ["1"]]:
                        #    I6 = I5
                        #    R6 = R5
                        #    for value in e2:
                        #        I6 = I6.modifyParam('e2', value, "push")
                        #        R6 = R6.modifyParam('e2', value, "push")
                        #        
                        #        setattr(O, str(I6), I6)
                        #        setattr(O, str(R6), R6)
                

OpArray = [x for x in O.__dict__.values() if type(x) == Op]

#count = 0
#createdOps = set()
# Add created invalid operations
#for op1 in OpArray:
#    for op2 in OpArray:
#        result = InsertRule.apply(OpArray, [op1, op2])
#        if result is None:
#            result = RemoveRule.apply(OpArray, [op1, op2])
#        if not result is None:
#            if len(result.C.getParam('e')) > 0:
#                createdOps.add(result.C)
#                count = count + 1

#OpArray = OpArray + list(createdOps)[0:500]

#%% Test for the full system
bestFoundGrid = None
entriesInBestGrid = 0

fullGridRun = findOperations(
    OpArray,
    [],
    rules
)

ops = gridToArray(fullGridRun[0])

print (ops.shape[0] * ops.shape[1] - np.count_nonzero(ops))
# Questions: What happens if SR is rebased with respect to I?
#            What happens if a Scaffolded operation is rebased with respect to another scaffolded op?
raise Error()
    

#%% Check for reordering compatibility
def ruleRebase(A, B):

    if B.name == 'I':
        result = InsertRule.apply(None,  [A, B])
    else:
        result = RemoveRule.apply(None,  [A, B])
    
    if result.invalid:
        raise Exception('Invalid Case!')
        
    return result.C

# Overwrite create Rule, to ignor non-grid entries
def createRule(grid, RuleConstructor, A, B, C, inputs, invalidCase=False):
    #if A == None or B == None or C==None:
    #    return None
    
    return RuleConstructor(A, B, C, inputs, invalidCase)

# Define Operations
class O:
    I = Op('I', 'R', ['i', 'p', 's', 'c', 'e','e2'], ["i", 0, [], 0, [], []])
    R = I.inv()

def applyOperationToString(op, s):
    position = op.getParam('p')
    if op.name == 'I':
        return s[0:position] + op.getParam('i') + s[position:]
    else:
        return s[0:position] + s[position + 1:]



for i in ["i", "j", "k", "l"]:
    I1 = O.I.modifyParam('i', i)
    R1 = O.R.modifyParam('i', i)
    for p in [ 0, 1, 2, 3, 4, 5, 6]:
        I2 = I1.modifyParam('p', p)
        R2 = R1.modifyParam('p', p)
        #for s in [[], ["i"], ["j"], ["i","j"]]:
        for s in [[]]:
            I3 = I2
            R3 = R2
            for value in s:
                I3 = I3.modifyParam('s', value, "push")
                R3 = R3.modifyParam('s', value, "push")

            for c in [0]:
           # for c in [-1, 0, 1]:
                I4 = I3.modifyParam('c', c)
                R4 = R3.modifyParam('c', c)
                
                for e in [[]]:
                    I5 = I4
                    R5 = R4
                    for value in e:
                        I5 = I5.modifyParam('e', value, "push")
                        R5 = R5.modifyParam('e', value, "push")
                    
                    setattr(O, str(I5), I5)
                    setattr(O, str(R5), R5)
                        #for e2 in [[], ["0"], ["1"]]:
                        #    I6 = I5
                        #    R6 = R5
                        #    for value in e2:
                        #        I6 = I6.modifyParam('e2', value, "push")
                        #        R6 = R6.modifyParam('e2', value, "push")
                        #        
                        #        setattr(O, str(I6), I6)
                        #        setattr(O, str(R6), R6)
                        

OpArray = [x for x in O.__dict__.values() if type(x) == Op]

#%% try all combinations to find ones with same effect on sequence
refOps = [O.__dict__["I_i_p+3"], O.__dict__["R_j_p+2"], O.__dict__["I_k_p+2"], O.__dict__["R_l_p+1"]]
def applyOpsToSequence(ops):
    seq = "abcdefg"
    for op in ops:
        seq = applyOperationToString(op, seq)
        
    return seq

expectedResult = applyOpsToSequence(refOps)
solutions = []
for O1 in OpArray:
    for O2 in OpArray:
        for O3 in OpArray:
            for O4 in OpArray:
                newSolution = applyOpsToSequence([O1, O2, O3, O4])
                if newSolution == expectedResult:
                    solutions.append([O1, O2, O3, O4])

#%% Compute for each solution the result for rebases
solutionResults = []

i = 0
for sol in solutions:
    print(i)
    i += 1
    rebaseResults = []
    for InputOp in OpArray:
        result = InputOp
        try:
            for op in sol:
                result = ruleRebase(result, op)
            rebaseResults.append("%s=%s" % (InputOp, result))
        except Exception as e:
                if e.args[0] == 'Invalid Case!':
                    pass
                else:
                    raise e
    solutionResults.append(",".join(rebaseResults))

#%% Find solutions that have the seame rebase result as the reference
refSolutionIndex = [i for i in range(len(solutions)) if ",".join([str(x) for x in solutions[i]]) == ",".join([str(x) for x in refOps])]

def compareSolutions(sol1, sol2):
    segments1 = sol1.split(',')
    segments2 = sol2.split(',')
    
    errors = 0

    for seg1 in segments1:
        if not seg1 in segments2:
            errors += 1

    for seg2 in segments2:
        if not seg2 in segments1:
            errors += 1

    return errors

errorCounts = [(compareSolutions(solutionResults[i], solutionResults[382]), i) for i in range(len(solutionResults))]
errorCounts.sort()

def solutionSorded(ops):
    for i in range(len(ops)):
        for j in range(i):
            if ops[i].getParam('p') < ops[j].getParam('p') - 1:
                return False
    return True

sortedErrors = [x for x in errorCounts if solutionSorded(solutions[x[1]])]



#errorCounts[9]
#Out[93]: (4, 249)

#[str(x) for x in solutions[249]]
#Out[94]: ['I_i_p+2', 'I_k_p+2', 'R_l_p+1', 'R_j_p+3']


#%% Operation combinations to test
failures = []
for A in OpArray:
    for B in OpArray:
        for C in OpArray:
            if A.getParam('p') < B.getParam('p'):
                continue
            #if A.getParam('p') == B.getParam('p') and (A.name == 'I' or B.name =='R'):
            #    continue
            #if A.getParam('p') == B.getParam('p') and not (A.name == 'R' and B.name =='I'):
            #    continue
            #if A.getParam('i') != 'i': continue
            #if B.getParam('i') != 'j': continue
            #if C.getParam('i') != 'k': continue
            #if A.getParam('p') == B.getParam('p') + 1 and B.name == 'R':
            #    continue
            if A.getParam('p') != B.getParam('p') or not (A.name == 'R' and B.name =='I'):
                continue
                
            try:
                #B_ = ruleRebase(B, A.inv() )
                #B_ = B#ruleRebase(B, A.inv() )
                #A_ = ruleRebase(A, B_)
                B_ = B
                A_ = A
                
                result1 = ruleRebase(ruleRebase(C, A), B)
                result2 = ruleRebase(ruleRebase(C, B_), A_)
                    
                if str(result1) != str(result2):
                    #print ("Incorrect result %s, %s, %s: %s != %s" % (str(A), str(B), str(C), str(result1), str(result2) ))
                    failures.append([A, B, C, A_, result1, result2])

            except Exception as e:
                if e.args[0] == 'Invalid Case!':
                    pass
                else:
                    raise e

#%% Test for the full system
bestFoundGrid = None
entriesInBestGrid = 0

fullGridRun = findOperations(
    [
     O.I, O.R,
     O.CI,O.CIInv,
     O.CI_1, O.CIInv_1,

     O.CR,O.CRInv,
     O.SI,O.SR,
     O.I_1, O.R_1,
     O.SCI,O.SCR,
     O.SI_1,O.SR_1,
     O.SI_P_1, O.SR_P_1
    ],
    [
      (O.I, O.I, O.CI),
      (O.CI, O.CI, O.CI_1),
      (O.R, O.R, O.CR),
      (O.CR, O.I, O.R),
      #(O.I, O.CR, O.CRInv),
      
      #(O.CRInv, O.I, O.CI_C2),
      #(O.CI_C2, O.R, O.CRInv),
      #(O.CRInv, O.R, O.I),
      #(O.R, O.I, O.R_1),
      #(O.R, O.CR, O.R),

      #(O.CR, O.R, O.SCR),
      #(O.CRInv, O.CR, O.SCI),
      #(O.SI, O.I, O.I),
      
      #(O.SI, O.R, O.SI_1),
      #(O.SR, O.SI, O.SR_1),
      #(O.SR, O.SR, O.CR_1),
      
      # Follows from I * R -> R = (I -> R) * (R -> R -> R -> (I->R) ) = SI^-1 = SCR -> SI
      #(O.SCR, O.SI, O.SR),
      
      #(O.I_1, O.R, O.I),
      #(O.R_1, O.R, O.R),
      #(O.R, O.R_1, O.R),

      #(O.R, O.R_1, O.SR.modifyParam('p', 1)),
      
      # Experiments I I
      #(O.I, O.I, O.SI_P_1),
      #(O.R, O.I, O.SR_P_1),
      #(O.SI_P_1, O.R, O.I),
      #(O.R, O.SI, O.SR_P_1),

      
      #(O.I, O.SR, O.SI),
      #(O.I_1, O.SR, O.I),
      #(O.SI, O.SR, O.SI_1),
      #(O.R, O.SR, O.CR),
      #(O.SI, O.SR, O.I),
      #(O.I, O.SI, O.I_1),


# Theories:
#      (O.SI, O.CR, O.SI_1),
#      (O.CR, O.CR, O.R),
#      (O.SI_1, O.SI, O.I),


#      (O.CI, O.I, O.CI),
#      (O.SR, O.I, O.SR),
      
#      (O.CI, O.R, O.SR),

      # Does R+1 ans I+1 swap with CI, CR, SR, SI?
      #(O.I_1, O.CR, O.I_1),
      #(O.I_1, O.CI, O.I_1),
      #(O.I_1, O.CR_1, O.I_1),
      #(O.I_1, O.CI_1, O.I_1),
      
      #(O.I_1, O.SR, O.I_1),
      #(O.I_1, O.SI, O.I_1),
      #(O.I_1, O.SR_1, O.I_1),
      #(O.I_1, O.SI_1, O.I_1),
      
      #(O.R_1, O.CR, O.R_1),
      #(O.R_1, O.CI, O.R_1),
      #(O.R_1, O.CR_1, O.R_1),
      #(O.R_1, O.CI_1, O.R_1),
      
      #(O.R_1, O.SR, O.R_1),
      #(O.R_1, O.SI, O.R_1),
      #(O.R_1, O.SR_1, O.R_1),
      #(O.R_1, O.SI_1, O.R_1),

    ],
    rules
)

ops = gridToArray(fullGridRun[0])

# Questions: What happens if SR is rebased with respect to I?
#            What happens if a Scaffolded operation is rebased with respect to another scaffolded op?
raise Error()
#%% Test for the syste where Z = CI
bestFoundGrid = None
entriesInBestGrid = 0

runWithZEqCi = backtrackingSearch(
    [
     O.I, O.R,
     O.CR,O.CI,
     O.Y, O.YInv
    ],
    [
      #(O.I, O.I, O.CI),
      #(O.I, O.R, O.Y),
      #(O.R, O.R, O.CR),
      #(O.CR, O.R, O.R),
      #(O.CR, O.CR, O.R)
    ],
    rules
)

ops = gridToArray(runWithZEqCi[0])

#%% Test for the syste where Z = CI, Y=CI
bestFoundGrid = None
entriesInBestGrid = 0

runWithZEqCiYEqCi = backtrackingSearch(
    [
     O.I, O.R,
     O.CR,O.CI
    ],
    [
      #(O.I, O.I, O.CI),
      #(O.I, O.R, O.CI),
      (O.R, O.R, O.CR),
      #(O.CR, O.R, O.R),
      #(O.CR, O.CR, O.R)
    ],
    rules,
    16
)

ops = gridToArray(runWithZEqCiYEqCi[3][0])

#%%
fullGridRun = backtrackingSearch(
    [
     O.I, O.R,
     O.CR,O.CI,
     O.Y, O.YInv,
    ],
    [
      (O.I, O.I, O.I),
      (O.R, O.I, O.R),
     (O.CR, O.I, O.CR),
     (O.CI, O.I, O.CI),
     (O.Y, O.I, O.Y),
     (O.YInv, O.I, O.YInv),
      #(O.I, O.CR, O.I),
      #(O.CR, O.CR, O.CR),
      #(O.Y, O.CR, O.Y),

      #(O.I, O.Y, O.I),
      #(O.CR, O.Y, O.CR),
      #(O.Y, O.Y, O.Y),
    ],
    rules
)
ops = gridToArray(fullGridRun[0])

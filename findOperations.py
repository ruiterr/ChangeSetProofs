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
            if value > 0:
                registrationName += '_' + name + '+' + str(value)
            if value < 0:
                registrationName += '_' + name  + str(value)
        
        return registrationName
    
    def modifyParam(self, name, delta):
        newParamValues = list(self.paramValues)
        paramIndex = self.paramNames.index(name)
        newParamValues[paramIndex] += delta
        
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

def createRule(grid, RuleConstructor, A, B, C):
    if A == None or B == None or C==None:
        return None
    
    if (not A in grid) or (not B in grid) or (not C in grid):
        return None
    
    return RuleConstructor(A, B, C)

def inv(A):
    if A == None:
        return None
    
    return A.inv()

def getOpListFromGrid(grid):
    OpList = grid.keys()
    
    return [(i, j, grid[i][j]) for i in OpList for j in OpList if grid[i][j] != None]
class Rule:
    def __init__(self, A, B, C):
        self.A = A
        self.B = B
        self.C = C
    

    @staticmethod 
    def getNumInputs():
        return 0
    
    @staticmethod 
    def apply(grid, operations):
        return None
    
    def str(self):
        return ""

class Rule1(Rule):
    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        U = rebase(grid, A, B)
        
        
        return createRule(grid, Rule1, U, inv(B), A)

class Rule2(Rule):

    @staticmethod 
    def getNumInputs():
        return 1
    
    @staticmethod 
    def apply(grid, operations):
        A = operations[0]
        Z = rebase(grid, A, A)
        
        
        return createRule(grid, Rule2, inv(A), Z, inv(Z))

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
        
        return createRule(grid, Rule3, V, W, inv(W))

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
        
        return createRule(grid, Rule4, V, B, W)

class Rule5(Rule):

    @staticmethod 
    def getNumInputs():
        return 2
    
    @staticmethod 
    def apply(grid, operations):
        A,B = operations
        X = findOpFromBandC(grid, B, A)
        
        return createRule(grid, Rule5, A, inv(B), X)

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
                
        return createRule(grid, Rule6, V, U, inv(U))

rules = [Rule1, Rule2, Rule3, Rule4, Rule5, Rule6]
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
                    currentEntry = grid[result.A][result.B]
                    
                    if currentEntry == result.C:
                        continue
                    if currentEntry == None:
                        if result.A in grid and result.B in grid[result.A]:
                            grid[result.A][result.B] = result.C
                            newEntryFound = True
                            appliedRules.append(result)
                            #print("New Entry Found")
                        continue
                    if currentEntry != result.C:
                        #print(len(ops))
                        print("Collision found for rule %s (input %s) operations: %s %s. Existing entry %s new Entry %s" % (r, ",".join([X.name for X in ops]), result.A.name, result.B.name, currentEntry.name, result.C.name))
                        return None
                    
    return (grid, appliedRules)

def gridToArray(grid):
    gridKeys = list(grid.keys())
    arr = []
    for i in range(len(gridKeys)):
        arr.append([])
        for j in range(len(gridKeys)):
            value = grid[gridKeys[j]][gridKeys[i]]
            
            if value == None:
                arr[i].append("")
            else:
                arr[i].append(str(value))
    
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
    I = Op('I', 'R', ['p', 's'])
    R = I.inv()
    I_1 = I.modifyParam('p', 1)
    R_1 = I_1.inv()
    CR = Op('CR', 'CI', ['p', 's'])
    CI = CR.inv()
    CR_1 = CR.modifyParam('s', 1)
    CI_1 = CR_1.inv()
    SI = I.modifyParam('s', 1)
    SR = SI.inv()
    SI_1 = SI.modifyParam('s', 1)
    SR_1 = SI_1.inv()
    

#%% Test for the full system
bestFoundGrid = None
entriesInBestGrid = 0

fullGridRun = findOperations(
    [
     O.I, O.R,
     O.CR,O.CI,
     O.SR,O.SI,
     O.I_1, O.R_1,
     O.CR_1,O.CI_1,
     O.SR_1,O.SI_1,
    ],
    [
      (O.I, O.I, O.I_1),
      (O.I, O.R, O.SI),
      (O.R, O.R, O.CR),
      (O.R, O.I, O.R_1),
      (O.R, O.CR, O.R),

      (O.CR, O.R, O.CR_1),
      (O.CI, O.CR, O.CI_1),
      (O.SI, O.I, O.I),
      
      (O.SI, O.R, O.SI_1),
      (O.SR, O.SI, O.SR_1),
      (O.SR, O.SR, O.CR_1),

      (O.I_1, O.R, O.I),
      (O.R_1, O.R, O.R),

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

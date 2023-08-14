# logicPlan.py
# ------------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
#
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from dis import dis
from pprint import PrettyPrinter
from typing import Dict, List, Tuple, Callable, Generator, Any

from numpy import extract, true_divide
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy

pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
ghost_pos_str = 'G'
ghost_east_str = 'GE'
pacman_alive_str = 'PA'
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict(
    [(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict(
    [(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North': (0, 1), 'South': (
    0, -1), 'East': (1, 0), 'West': (-1, 0)}


# ______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    A or B
    (not A) if and only if ((not B) or C)
    ¬ A ↔ (¬ B or C)
    (not A) or (not B) or C
    ¬ A or ¬ B or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    a_or_b = disjoin(A, B)
    noA_impnoBC = (~A) % (~B | C)

    not_ABC = disjoin(~A, ~B, C)

    return conjoin(a_or_b, noA_impnoBC, not_ABC)
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    D = Expr('D')

    c_iif_BC = C % (B | D)
    a_imp_BD = A >> (~B & ~D)
    notBC_impA = (~(B & ~C)) >> A
    notD_impC = (~D) >> C

    return conjoin(c_iif_BC, a_imp_BD, notBC_impA, notD_impC)
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):
    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.
    Pacman cannot both be alive at time 0 and be born at time 0.
    Pacman is born at time 0.
    (Project update: for this question only, [0] and _t are both acceptable.)
    """
    "*** BEGIN YOUR CODE HERE ***"
    Alive1 = PropSymbolExpr("PacmanAlive_1")
    Alive0 = PropSymbolExpr('PacmanAlive_0')
    Born0 = PropSymbolExpr('PacmanBorn_0')
    Killed0 = PropSymbolExpr('PacmanKilled_0')

    aliveNow = Alive1 % disjoin(
        conjoin(Alive0, ~Killed0), conjoin(~Alive0 & Born0))
    noboth = conjoin(Alive0, Born0)
    return conjoin(aliveNow, ~noboth, Born0)

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)


def findModelCheck() -> Dict[Any, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    This can be solved with a one-line return statement.
    """
    class dummyClass:
        """dummy('A') has representation A, unlike a string 'A' that has repr 'A'.
        Of note: Expr('Name') has representation Name, not 'Name'.
        """

        def __init__(self, variable_name: str = 'A'):
            self.variable_name = variable_name

        def __repr__(self):
            return self.variable_name
    "*** BEGIN YOUR CODE HERE ***"
    return {dummyClass("a"): True}
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"
    if (not findModel(conjoin(premise, ~conclusion))):
        return True
    else:
        return False

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    return pl_true(~inverse_statement, assignments)

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

# ______________________________________________________________________________
# QUESTION 2


def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals  ist is true.
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    return disjoin(literals)
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    if len(literals) == 1:
        return literals
    conjunctions = []

    literal_pairs = list(itertools.combinations(literals, 2))

    for pair in literal_pairs:
        disjunction = disjoin(~pair[0], ~pair[1])
        conjunctions.append(disjunction)

    return conjoin(conjunctions)
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    return conjoin(atLeastOne(literals), atMostOne(literals))
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

# ______________________________________________________________________________
# QUESTION 3


def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]] = None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    now, last = time, time - 1
    # enumerate all possible causes for P[x,y]_t
    possible_causes: List[Expr] = []
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x, y+1, time=last)
                               & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x, y-1, time=last)
                               & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x+1, y, time=last)
                               & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append(PropSymbolExpr(pacman_str, x-1, y, time=last)
                               & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None

    "*** BEGIN YOUR CODE HERE ***"

    return PropSymbolExpr(pacman_str, x, y, time=now) % atLeastOne(possible_causes)

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    moved_causes: List[Expr] = []
    if walls_grid[x][y+1] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x, y-1, time=last)
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x+1, y, time=last)
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append(PropSymbolExpr(pacman_str, x-1, y, time=last)
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(
        pacman_str, x, y, time=last), ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    # using merged variables, improves speed significantly
    failed_move_causes: List[Expr] = []
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(
            wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(
            wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(
            wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    
    pacphysics_sentences = []

    for coords in all_coords:
        x, y = coords[0], coords[1]
        wallLogic = PropSymbolExpr(wall_str, x, y) >> ~PropSymbolExpr(
            pacman_str, x, y, time=t)
        pacphysics_sentences.append(wallLogic)

    possible_locations = []
    for coords in non_outer_wall_coords:
        x, y = coords[0], coords[1]
        possible_locations.append(PropSymbolExpr(pacman_str, x, y, time=t))
    pacphysics_sentences.append(exactlyOne(possible_locations))

    possibleMoves = [PropSymbolExpr('North', time=t), PropSymbolExpr(
        'South', time=t), PropSymbolExpr('East', time=t), PropSymbolExpr('West', time=t)]
    pacphysics_sentences.append(exactlyOne(possibleMoves))
    if sensorModel != None:
        pacphysics_sentences.append(sensorModel(t, non_outer_wall_coords))
    if t > 0:
        if successorAxioms != None:
            pacphysics_sentences.append(successorAxioms(
                t, walls_grid, non_outer_wall_coords))
    return conjoin(pacphysics_sentences)
    "*** BEGIN YOUR CODE HERE ***"
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()

    all_coords = list(itertools.product(
        range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(
        range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]

    "*** BEGIN YOUR CODE HERE ***"
    mapLogic = conjoin(map_sent)
    KB.append(mapLogic)

    location0Logic = PropSymbolExpr(pacman_str, x0, y0, time=0)
    location1Logic = PropSymbolExpr(pacman_str, x1, y1, time=1)
    action0Logic = PropSymbolExpr(action0, time=0)
    action1Logic = PropSymbolExpr(action1, time=1)

    physicsLogic0 = pacphysicsAxioms(
        0, all_coords, non_outer_wall_coords, walls_grid, successorAxioms=allLegalSuccessorAxioms)
    physicsLogic1 = pacphysicsAxioms(
        1, all_coords, non_outer_wall_coords, walls_grid, successorAxioms=allLegalSuccessorAxioms)

    KB.append(physicsLogic0)
    KB.append(physicsLogic1)
    KB.append(location0Logic)
    KB.append(action0Logic)
    KB.append(action1Logic)
    kbLogic = conjoin(KB)
    
    return (findModel(conjoin(kbLogic, location1Logic)), findModel(conjoin(kbLogic, ~location1Logic)))

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

# ______________________________________________________________________________
# QUESTION 4


def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2),
                                        range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = ['North', 'South', 'East', 'West']
    KB = []
   
    "*** BEGIN YOUR CODE HERE ***"

    KB.append(PropSymbolExpr(pacman_str, x0, y0, time = 0)) #use propsymbolexpr, not correct syntax, always make sure to append expr
    for t in range(50):
        print(t)
        #for one in non_wall_coords:
        propExpr = []
        for x, y in non_wall_coords:
            propExpr.append(PropSymbolExpr(pacman_str, x, y, time = t))
        KB.append(exactlyOne(propExpr))
        goal_assertion = PropSymbolExpr(pacman_str, xg, yg, time=t)
        #KB.append(go)
        model = findModel(conjoin([goal_assertion] + KB))  
        if model:
            return extractActionSequence(model, actions)
            
        #pacman can only take one action per timestep  
        conjoined = []
        for action in actions:
            conjoined.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(conjoined))
        for x, y in non_wall_coords:
                KB.append(pacmanSuccessorAxiomSingle(x, y, t + 1, walls_grid))
    return None


    "*** END YOUR CODE HERE ***"

# ______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = ['North', 'South', 'East', 'West']

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    KB.append(PropSymbolExpr(food_str, x0, y0, time = 0)) 
    for x, y in food:
        KB.append(PropSymbolExpr(food_str, x, y, time = 0)) 
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time = 0)) 
    #KB.append(PropSymbolExpr(food_str, x0, y0, time = 0)) 
    for t in range(50):
        print(t)

        propExpr = []
        for x, y in non_wall_coords:
            propExpr.append(PropSymbolExpr(pacman_str, x, y, time = t))
        KB.append(exactlyOne(propExpr))

        foods = []
        for x, y in food:
            foods.append(PropSymbolExpr(food_str, x, y, time = t))
        #KB.append(exactlyOne(foods)) #maybe not
        goal_assertion = ~disjoin(foods) #disjoin??

        model = findModel(conjoin([goal_assertion] + KB))
        if model:
            return extractActionSequence(model, actions) #program dies upon entering here

        action_lst = [] #im not conjoining here
        for action in actions:
            action_lst.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(action_lst))

        #for x, y in non_wall_coords:
        #    KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls_grid))

        for x, y in non_wall_coords:
            KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls))
            food_pres_t = PropSymbolExpr(food_str, x, y, time = t)
            pacman_pres = PropSymbolExpr(pacman_str, x, y, time=t)
            food_still_pres = PropSymbolExpr(food_str, x, y, time=t+1)
            KB.append((food_pres_t & ~pacman_pres) >> food_still_pres) #food present AND pacman not there, then food still present
            KB.append((food_pres_t & pacman_pres) >> ~food_still_pres)
            #KB.append((~food_pres_t & pacman_pres) >> ~food_still_pres)
            #KB.append(pacmanSuccessorAxiomSingle(x, y, t+1, walls_grid))

    return None

    "*** END YOUR CODE HERE ***"

# ______________________________________________________________________________
# QUESTION 6


def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(
        range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(
        range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []
    "*** BEGIN YOUR CODE HERE ***"

    #add to KB where the walls are wall_list and aren't in wallList
    for coors in walls_list:
        KB.append(PropSymbolExpr(wall_str, coors[0], coors[1]))
    
    for coors in all_coords:
        if coors not in walls_list:
            KB.append(~PropSymbolExpr(wall_str, coors[0], coors[1]))
    
    for t in range(agent.num_timesteps):
        print(t)
        #add pacphysics, action, and percept information to KB
        ##add pacphysics_axioms using sensorAxioms, and AllLegalsuccessorAxiom
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, walls_grid, 
                sensorAxioms, allLegalSuccessorAxioms))
        
        ##Pacman takes action prescribed by agent.actions[t]
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        
        ##calling get.Percept and pass it to fourbitPerceptRules and 
        #add the resulting percepts to KB 
        KB.append(fourBitPerceptRules(t, agent.getPercepts()))
       

        #find posisble pacman locations with updated KB
        possible_locations = []
        ##iterate over non_outer_wall_coords
        for coors in non_outer_wall_coords:
            ###can we prove whether Pacman is at (x,y)? can we prove wheter pacman is not (x,y)? Use entails and KB
             ### there exists a satisfying agsignment where pacman is at (x,y) at time t, add (x,y) to possible locations
            if entails(conjoin(KB), PropSymbolExpr(pacman_str, coors[0], coors[1], time = t)):
                ### add to KB (x, y) locations where Pacman is provably at, at time t
                KB.append(PropSymbolExpr(pacman_str, coors[0], coors[1], time = t))
            if entails(conjoin(KB), ~PropSymbolExpr(pacman_str, coors[0], coors[1], time = t)):
                ##add to KB  (x, y) locations where Pacman is provably not at, at time t.
                KB.append(~PropSymbolExpr(pacman_str, coors[0], coors[1], time = t))
            if findModel(conjoin(PropSymbolExpr(pacman_str, coors[0], coors[1], time = t), conjoin(KB))):
                possible_locations.append(coors)                
        #call agent.moveToNextState(action_t) on current agent action at timestep t
        agent.moveToNextState(agent.actions[t]) 

        "*** END YOUR CODE HERE ***"
        #yield possible locations
        yield possible_locations
    util.raiseNotDefined()

# ______________________________________________________________________________
# QUESTION 7


def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(
        range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(
        range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)]
                 for x in range(problem.getWidth()+2)]
   
    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    #get initial location of pacman and add to KB
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time = 0))
    #assuming wherever pacman starts there is no wall
    KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))
    known_map[pac_x_0][pac_y_0] = 0
    # for t in agent time steps
    for t in range(agent.num_timesteps):
        print(t)
        #add pacphysics, action, and percept information to KB
        ##add pacphysics_axioms using sensorAxioms, and AllLegalsuccessorAxiom
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, 
                sensorAxioms, allLegalSuccessorAxioms))
        ##Pacman takes action prescribed by agent.actions[t]
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        ##calling get.Percept and pass it to fourbitPerceptRules and 
        #add the resulting percepts to KB 
        KB.append(fourBitPerceptRules(t, agent.getPercepts()))

        for coors in non_outer_wall_coords:
            ###can we prove whether Pacman is at (x,y)? can we prove wheter pacman is not (x,y)? Use entails and KB
             ### there exists a satisfying agsignment where pacman is at (x,y) at time t, add (x,y) to possible locations
            if entails(conjoin(KB), PropSymbolExpr(wall_str, coors[0], coors[1])):
                ##add to KB and update knownmap that (x, y) is probably a wall.
                known_map[coors[0]][coors[1]] = 1
                KB.append(PropSymbolExpr(wall_str, coors[0], coors[1]))

            if entails(conjoin(KB), ~PropSymbolExpr(wall_str, coors[0], coors[1])):
                ##add to KB and update knownmap that (x, y) is probably not a wall.
                known_map[coors[0]][coors[1]] = 0
                KB.append(~PropSymbolExpr(wall_str, coors[0], coors[1]))
            
        agent.moveToNextState(agent.actions[t])
        "*** END YOUR CODE HERE ***"
        
        yield known_map

    util.raiseNotDefined()

# ______________________________________________________________________________
# QUESTION 8


def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(
        range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(
        range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)]
                 for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    # get initial location of pacman and add to KB
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time = 0))
    known_map[pac_x_0][pac_y_0] = 0
    KB.append(~PropSymbolExpr(wall_str, pac_x_0, pac_y_0))

    for t in range(agent.num_timesteps):
        print(t)
        #add pacphysics, action, and percept information to KB
        ##add pacphysics_axioms using sensorAxioms, and AllLegalsuccessorAxiom
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, 
                SLAMSensorAxioms, SLAMSuccessorAxioms))
        
        ##Pacman takes action prescribed by agent.actions[t]
        KB.append(PropSymbolExpr(agent.actions[t], time=t))
        
        ##calling get.Percept and pass it to fourbitPerceptRules and 
        #add the resulting percepts to KB 
        KB.append(numAdjWallsPerceptRules(t, agent.getPercepts()))
       
        #find posisble pacman locations with updated KB
        
        for coors in non_outer_wall_coords:
            ###can we prove whether Pacman is at (x,y)? can we prove wheter pacman is not (x,y)? Use entails and KB
             ### there exists a satisfying agsignment where pacman is at (x,y) at time t, add (x,y) to possible locations
            if entails(conjoin(KB), PropSymbolExpr(wall_str, coors[0], coors[1])):
                ##add to KB and update knownmap that (x, y) is probably a wall.
                known_map[coors[0]][coors[1]] = 1
                KB.append(PropSymbolExpr(wall_str, coors[0], coors[1]))
            if entails(conjoin(KB), ~PropSymbolExpr(wall_str, coors[0], coors[1])):
                ##add to KB and update knownmap that (x, y) is probably not a wall.
                known_map[coors[0]][coors[1]] = 0
                KB.append(~PropSymbolExpr(wall_str, coors[0], coors[1]))

        possible_locations = []
        for coors in non_outer_wall_coords:
            ###can we prove whether Pacman is at (x,y)? can we prove wheter pacman is not (x,y)? Use entails and KB
             ### there exists a satisfying agsignment where pacman is at (x,y) at time t, add (x,y) to possible locations
            if entails(conjoin(KB), PropSymbolExpr(pacman_str, coors[0], coors[1], time = t)):
                ### add to KB (x, y) locations where Pacman is provably at, at time t
                KB.append(PropSymbolExpr(pacman_str, coors[0], coors[1], time = t))
            if entails(conjoin(KB), ~PropSymbolExpr(pacman_str, coors[0], coors[1], time = t)):
                ##add to KB  (x, y) locations where Pacman is provably not at, at time t.
                KB.append(~PropSymbolExpr(pacman_str, coors[0], coors[1], time = t))
            if findModel(conjoin(PropSymbolExpr(pacman_str, coors[0], coors[1], time = t), conjoin(KB))):
                possible_locations.append(coors)       

        agent.moveToNextState(agent.actions[t])
        "*** END YOUR CODE HERE ***"
        yield (known_map, possible_locations)


# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

# ______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(
                pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(
            blocked_str_map[direction], time=t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(
            blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(
                blocked_str_map[direction], time=t)
        # The actual sensor readings
        percept_unit_clauses.append(percept_unit_clause)
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(
                pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(
                pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(
            blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t)
                    for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

# ______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False"
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    # return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width,
                         problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width,
                         problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)


class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).
    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()

    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()
------- 1
-- A = {(a1,b1), (a2,b1), (a2,a1), (b1,a2)}
-- B = {(b1,b1), (a2,b1), (a2,a1), (b1,a2)}
-- C = {(a1),(b1)}

-- (B :> C) = {(b1,b1), (b1, a2)}
-- (A :> C) = {(a1,b1), (b1, a2)}

-- C.A = {(b1), (a2)}

-- ^B = {(b1, b1), (a2, b1), (a2, a1), (b1, a2), (a2, a2), (b1, a1)}
-- C.^B = {(b1), (a2), (a1)}

-- ^A = {(a1, b1), (a2, b1), (a2, a1), (b1, a2), (a1, a2), (a2, a2), (a1, a1), (b1, b1), (not sure if there are more, iether way its true) }
-- iden = {(a1, a1), (a2, a2), (b1, b1)}

-------- 2
-- D = {(x1,y2), (x2,y3), (x2,y2), (x3,x1)}
-- E = {(x1),(x2),(y2)}
-- F = {(x1,y1), (x2,y1)}

-- Writing rel.Set is equivalent to writing Set.~rel
-- D.E = {(x1), (x2), (x3)}
-- E.D = {(y2), (y3)}

-- D ++ (E -> E) = {(x1,y2), (x2,y3), (x2,y2), (x3,x1)} ++ {(x1, x1), (x2, x2), (y2, y2)}
--      = {(x1, x1), (x2, x2), (x3, x1), (y2, y2)}

-- (D - F) :> E = {(x1,y2), (x2,y3), (x2,y2), (x3,x1)} :> {(x1),(x2),(y2)}
--      = {(x2, y2), (x3, x1)}

-- *D = {(x1,y2), (x2,y3), (x2,y2), (x3,x1), (x1, x1), (x2, x2), (x3, x3), (y2, y2), (y3, y3)}
-- D.~F = D.{(y1,x1), (y1,x2)} = {}

-------- nao me apetece fazer mais :(

-------- 11
open util/ordering[ProjectState]

sig Task {}
sig Worker {}
sig Project {
  tasks: some Task,           -- a project has one or more tasks
  workers: some Worker,       -- a project has one or more workers
  dependencies: tasks->tasks  -- pairs (t1,t2), meaning that t1
                              --  cannot start before t2 finishes, i.e.,
                              --  t1 depends on t2
}{
  no ^dependencies & iden -- dependencies are acyclic
}

sig ProjectState {
  project: Project,
  finished: set Task,
  ongoing: Task lone -> lone Worker   -- pairs (t,w), meaning that t
                                      --  is being carried out by w
                                      --  lone because a task can exist
                                      --  and not be ongoing
}{
  -- a) finished and ongoing tasks must belong to the project
  finished + ongoing.Worker in project.tasks
  -- b) finished and ongoing tasks must be disjoint
  no finished & ongoing.Worker
  -- c) dependencies of ongoing tasks must be finished
  -- wrong, becasue
  -- project.dependencies[ongoing.Worker] gives us the
  -- project dependencies of ongoing tasks
  -- they should be in finished set
  -- so a correct rule would be something like:
  --  project.dependencies[ongoing.Worker] in finished
  -- or
  --  project.dependencies[ongoing.Worker] = finished
  no project.dependencies[ongoing.Worker] & finished
  -- d) workers of ongoing tasks must belong to the project
  Task.ongoing in project.workers
}

-- Task t is started by worker w, changing project state from s to s'.
pred startTask[s, s': ProjectState, t: Task, w: Worker] {
  -- pre-conditions
  t in s.project.tasks -- a) t is a task of project 
  t not in s.finished + s.ongoing -- b) t is not finished and ongoing
  Task->w not in s.ongoing -- c) wrong (what they probably want to prove is that w is not assigned to any task)
  s.project.dependencies[t] in s.finished -- d) t's dependecies are finished

  -- post-conditions
  s'.project = s.project and s'.finished = s.finished
  s'.ongoing = s.ongoing + t -> w
}

-- RANDOM NOTE: L.state[C] = C.(L.state) = (L.state)[C]

-- Task t is finished by worker w, changing project state from s to s'.
pred finishTask[s, s': ProjectState, t: Task, w: Worker] {
  -- pre and post-conditins
  t->w in s.ongoing -- a) pre-condition: t is allocated to w and ongoing in s
  s'.project = s.project -- b) post-conditions: the project remains the same
  s'.finished = s.finished + t -- c) post-condition: t is finished in s'
  s'.ongoing = t <: s.ongoing :> w -- d) post-conditions: idk, but it seems weird
                                   -- something simple like s'.ongoing = s.ongoing - t->w would do the trick (I think)
}

-- The ordered instances of ProjectState must represent a valid
-- execution of a project.
fact validOrdering {
  -- a) in the first state, there are no finished tasks
  no first.finished
  -- b) in the first state, there are no ongoing tasks
  no first.ongoing
  -- c) consecutive states are related by startTask or finishTask
  s: ProjectState, s' : s.next | some t: Task, w: Worker |
    startTask[s, s', t, w] or finishTask[s,s', t, w]
  -- d) in the last state, all tasks are finished
  all last.finished -- wrong
}

run { some dependencies } for 5

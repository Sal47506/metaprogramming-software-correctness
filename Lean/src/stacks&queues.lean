import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

set_option autoImplicit true

universe u
variable {α : Type u}

structure Stack (α : Type u) :=
  (data : List α)
deriving Repr

namespace Stack

def empty : Stack α := ⟨[]⟩

def push (x : α) (s : Stack α) : Stack α :=
  ⟨x :: s.data⟩

def pop (s : Stack α) : Option (α × Stack α) :=
  match s.data with
  | [] => none
  | x :: xs => some (x, ⟨xs⟩)

end Stack

theorem pop_push (x : α) (s : Stack α) :
  Stack.pop (Stack.push x s) = some (x, s) := by
  simp [Stack.push, Stack.pop]

macro "stacks" : tactic =>
  `(tactic| simp [Stack.push, Stack.pop])


structure Queue (α : Type u) :=
  (data : List α)
deriving Repr

namespace Queue

def push (x : α) (q : Queue α) : Queue α :=
  ⟨x :: q.data⟩

def pop (q : Queue α) : Option (α × Queue α) :=
  match q.data with
  | [] => none
  | x :: xs => some (x, ⟨xs⟩)

end Queue

macro "queues" : tactic =>
  `(tactic| simp [Queue.push, Queue.pop])

theorem queue_pop_push (x : α) (q : Queue α) :
  Queue.pop (Queue.push x q) = some (x, q) := by
  queues


macro "mk_pop_push " T:ident push:ident pop:ident thm:ident : command =>
  `(
    theorem $thm {α} (x : α) (s : $T α) :
      $pop ($push x s) = some (x, s) := by
      simp [$push:ident, $pop:ident]
  )

mk_pop_push Stack Stack.push Stack.pop stack_correct
mk_pop_push Queue Queue.push Queue.pop queue_correct

import Mathlib

set_option autoImplicit false
set_option tactic.hygienic false

structure TimeM (α : Type) where
  ret : α
  time : ℕ

namespace TimeM

-- Take type and associate it with 0 (time)
def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩ -- we don't do anything with the time

-- Take object and function that manipulates it
def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret -- take type, apply function
  ⟨r.ret, m.time + r.time⟩ -- take the result of the function, and add times together

-- define this to allow using lean monads?
instance : Monad TimeM where
  pure := pure
  bind := bind

-- Define some helpers...

-- Increment time
@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

-- We can define this notation to say "increase 1 to the running type..."
notation "✓" a:arg ", " c:arg => tick a c
notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1

@[grind, simp] theorem time_of_pure {α} (a : α) : (pure a).time = 0 := rfl
@[grind, simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[grind, simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure


end TimeM

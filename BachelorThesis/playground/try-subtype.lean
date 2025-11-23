import Mathlib.Data.Real.Basic

namespace Point
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

/- automatically generate theorem of extensionality,
  two instance of structure are equal when their components are equal -/
#check Point.ext

def myPoint :=
  Point.mk 2 3 4 --Point.mk is the constructor of structure Point
#check myPoint

structure Point' where constructor :: --makes the .mk constructor explicit
  x : ℝ
  y : ℝ
  z : ℝ
def myPoint' :=
  Point'.constructor 2 3 4
#check myPoint'

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw[add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]
end Point


-- *algebraic abstraction*

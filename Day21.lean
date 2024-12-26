import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Array Char))
  := (anyChar.until (string "\n")).many
end Parser

def keypad : Char -> Int × Int
  | '7' => (-2, -3)
  | '8' => (-1, -3)
  | '9' => (0, -3)
  | '4' => (-2, -2)
  | '5' => (-1, -2)
  | '6' => (0, -2)
  | '1' => (-2, -1)
  | '2' => (-1, -1)
  | '3' => (0, -1)
  | '0' => (-1, 0)
  | 'A' => (0, 0)
  | _ => (0, 0)

def keypad.gap : Int × Int := (-2, 0)

def dpad : Dir4 → Int × Int
  | .N => (-1, 0)
  | .S => (-1, 1)
  | .E => (0, 1)
  | .W => (-2, 1)

def dpad.gap : Int × Int := (-2, 0)

structure Costs where
  e : Nat
  se : Nat
  es : Nat
  s : Nat
  sw : Nat
  ws : Nat
  w : Nat
  nw : Nat
  wn : Nat
  n : Nat
  ne : Nat
  en : Nat

def Costs.move (c : Costs) (gap : Int × Int) (p₁ : Int × Int) (p₂ : Int × Int)
  : Nat :=
    let δ := (p₁.1 - p₂.1).natAbs + (p₁.2 - p₂.2).natAbs
    let corner hv vh := if gap = (p₂.1, p₁.2)
      then vh
      else if gap = (p₁.1, p₂.2)
        then hv
        else min vh hv
    match compare p₁.1 p₂.1, compare p₁.2 p₂.2 with
    | .lt, .lt => corner c.es c.se + δ
    | .lt, .eq => c.e + δ
    | .lt, .gt => corner c.en c.ne + δ
    | .eq, .lt => c.s + δ
    | .eq, .eq => 0
    | .eq, .gt => c.n + δ
    | .gt, .lt => corner c.ws c.sw + δ
    | .gt, .eq => c.w + δ
    | .gt, .gt => corner c.wn c.nw + δ

def Costs.dpadLayer (c : Costs) : Costs :=
  { e := one .E
  , se := two .S .E
  , es := two .E .S
  , s := one .S
  , sw := two .S .W
  , ws := two .W .S
  , w := one .W
  , nw := two .N .W
  , wn := two .W .N
  , n := one .N
  , ne := two .N .E
  , en := two .E .N
  }
  where
    one d := c.move dpad.gap (0, 0) (dpad d) + c.move dpad.gap (dpad d) (0, 0)
    two d₁ d₂ := c.move dpad.gap (0, 0) (dpad d₁)
      + c.move dpad.gap (dpad d₁) (dpad d₂)
      + c.move dpad.gap (dpad d₂) (0, 0)

def Costs.direct : Costs := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def Costs.type (c : Costs) : List (Int × Int) → Nat :=
  let rec go p
    | p' :: ps => c.move keypad.gap p p' + 1 + go p' ps
    | [] => 0
  go (0, 0)

def solution (c : Costs) : Array (Array Char) → Nat
  | codes => codes.foldl
    (λsum code =>
      let numeric := code.foldl
        (λn d => if d.isDigit then n * 10 + (d.toNat - '0'.toNat) else n)
        0
      let presses := c.type (keypad <$> code.toList)
      sum + numeric * presses
    )
    0

def solution1 : Array (Array Char) → Nat
  := solution Costs.direct.dpadLayer.dpadLayer

def solution2 : Array (Array Char) → Nat
  := solution $ Nat.rec Costs.direct (λ_ => Costs.dpadLayer) 25

def main : IO Unit := IO.main parser solution1 solution2

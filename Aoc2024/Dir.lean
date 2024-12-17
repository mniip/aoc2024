inductive Dir4 : Type where
  | E
  | S
  | W
  | N
  deriving BEq, Ord

def Dir4.list : List Dir4 := [E, S, W, N]

def Dir4.transform
  : Dir4 → (along : Int) → (ccw : Int) → (org : Int × Int) → Int × Int
  | d, along, ccw, (oX, oY) => match d with
    | E => (oX + along, oY - ccw)
    | S => (oX + ccw, oY + along)
    | W => (oX - along, oY + ccw)
    | N => (oX - ccw, oY - along)

def Dir4.transform'
  : Dir4 → (along : Int) → (ccw : Int) → (org : α × β)
    → [CoeT α org.1 Int] → [CoeT β org.2 Int] → Int × Int
  | d, along, ccw, (oX, oY), _, _ => d.transform along ccw (oX, oY)

def Dir4.advanceBy : Dir4 → Int → Int × Int → Int × Int
  | d, dist => d.transform dist 0

def Dir4.advance : Dir4 → Int × Int → Int × Int
  | d => d.advanceBy 1

def Dir4.advance'
  : Dir4 → (p : α × β) → [CoeT α p.1 Int] → [CoeT β p.2 Int] → Int × Int
  | d, (x, y), _, _ => d.advance (x, y)

def Dir4.delta : Dir4 → Int × Int
  | d => d.advance (0, 0)

def Dir4.cw : Dir4 → Dir4
  | E => S
  | S => W
  | W => N
  | N => E

def Dir4.ccw : Dir4 → Dir4
  | E => N
  | S => E
  | W => S
  | N => W

inductive Dir8 : Type where
  | E
  | SE
  | S
  | SW
  | W
  | NW
  | N
  | NE
  deriving BEq, Ord

def Dir8.list : List Dir8 := [E, SE, S, SW, W, NW, N, NE]

def Dir8.advanceBy : Dir8 → Int → Int × Int → Int × Int
  | d, dist, (x, y) => match d with
    | E => (x + dist, y)
    | SE => (x + dist, y + dist)
    | S => (x, y + dist)
    | SW => (x - dist, y + dist)
    | W => (x - dist, y)
    | NW => (x - dist, y - dist)
    | N => (x, y - dist)
    | NE => (x + dist, y - dist)

def Dir8.advance : Dir8 → Int × Int → Int × Int
  | d => d.advanceBy 1

def Dir8.delta : Dir8 → Int × Int
  | d => d.advance (0, 0)

def Dir8.cw : Dir8 → Dir8
  | E => SE
  | SE => S
  | S => SW
  | SW => W
  | W => NW
  | NW => N
  | N => NE
  | NE => E

def Dir8.ccw : Dir8 → Dir8
  | E => NE
  | SE => E
  | S => SE
  | SW => S
  | W => SW
  | NW => W
  | N => NW
  | NE => N

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyBorders.lean: the table of joints of the key file: the form for all three chains, and the first chain's rows: what the state that each block of the key file's description hands to the
next means. In the form of the table of the proof file's first chain (Johnson/Desc/First/Borders.lean): a border lies in front of each block of `Chain.blocksInOrder` and behind the last; the relation at a
border is computed: «every open item holds»; an item is a named claim on one witness for the whole file; a block's row says which items it closes (ins), opens (outs), reads and leaves (ctx), and which components
of the witness the table's one extractor lays there. Definitions alone; without Mathlib; it imports Johnson/Desc/Msg.lean (Strs · Wit · Reading · PIN · NoColl · PINW).
At which cut: F_K := KeyFinal.fkOf, a description of the key file that is not in this library: 19 | 12 | 4 blocks [by one run at small public files, not at this tree's own: F.places]. The blocks are named here by their names there.
The witness: Wit Cells Unit M: cells: the stored table's message (the matrix M with its pads) · msg k: 0 I (the index-mask message) · 1 B (the lookups' own message: the planes of the counts' bits; its mask rows) ·
2 V (the message that the format calls W: gᵀM) · 3 U (G_u) · 4 Omega · 5 the shared split's mask message. A proximity test's inner messages are no components: each test is one block here.
Where the key file's table parts from the proof file's. There «the stored table decodes with the record» stands in every promise. Here it is the goal: it is the item pinT, open from the first border until the
shared chain closes it; the promise holds of the stored table only «no collision at the record's seed» (the first border's condition).
  KItem · KRow · stepOpen · openSets · readsOpen · lastOpen    the form (the proof file's, at KItem)
  names₁ · rows₁ · start₁ · end₁                                 the first chain: its nineteen blocks' names, their rows, what is open in front of it and behind it
  KMeaning · KItem.holds · onAt                                  what an item says: letters, one a sort of item; while a letter stands open, a row over it says nothing
The shared and the second chain's rows: Johnson/Desc/Key/KeyBorders23.lean, over the open constructor `claim`.
Limits. A skeleton. No row is confirmed. No law is stated here, none proved. Nothing on soundness; nothing on hiding.
-/
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-! ## 1 The items -/

/-- **An item**: a named claim on the one witness. -/
inductive KItem where
  /-- the carried record bears no deferred mark -/
  | unmarked
  /-- THE GOAL's FIRST HALF: the stored table decodes, with its record, to the witness's cells -/
  | pinT
  /-- THE GOAL's SECOND HALF, lookup by lookup: every key that lookup l reads off the witness's cells is a row of that lookup's table -/
  | inRange (l : Nat)
  /-- message k of the witness is a member of its committed word's list that meets its sample -/
  | pin (k : Nat)
  /-- the fresh mask that is sent ahead in message k's tree (a tenant WITHOUT a sample) is near a word of its code: under its own «there is». IN NO ROW OF THE KEY FILE: the library's joint
  behind a sending asks nothing of a mask sent ahead and raises it inside the test: so it stands INSIDE K12's ROW. The constructor stays for the one form with the proof file's table. -/
  | near (k : Nat)
  /-- message k's sample rows (its answers at its seed, with its pad) hold at the witness: OWED TO THE PROXIMITY TEST ON ITS GROUP -/
  | srow (k : Nat)
  /-- lookup l: every form behind that run of K3's claims is worth 0 in the world of the lookup's ledger and the witness -/
  | forms (l : Nat) (run : String)
  /-- lookup l: K3's own forms, fed with the TRUE values of the committed messages at the points heard, are worth 0: "planes": the planes of the counts' bits at the two points, and the counts' sum; "keys": each
  part's key vector at its key point -/
  | worth (l : Nat) (what : String)
  /-- lookup l's rows, as the layer lays them into the state, hold at the witness: linear equations, with public targets, on B's planes and on mask entries -/
  | rows (l : Nat)
  /-- lookup l's claims on its parts' keys hold at the witness: for each part: ⟨the part's vector at its point, the cells⟩ + (mask entries of I) = target -/
  | kclaims (l : Nat)
  /-- all open rows of the statement's group of B hold at the witness -/
  | grows
  /-- THE ONE CLAIM THAT THE BATCHING LEAVES. IT RIDES ACROSS V's SENDING AND THE SEAM, OPEN, AND CLOSES WHERE THE SHARED POINT IS DRAWN (as the library's own joint behind that sending has it: Cb/Ld/LdLin.lean's j1, by reading;
  and as the table of Johnson/Desc/First/Borders.lean has it at the proof file): ⟨g ⊗ eq(psi_c, ·), the cells' matrix⟩ + (mask entries of I) = target -/
  | pile
  /-- an item of a later chain, by its name -/
  | claim (chain : Nat) (name : String)
  deriving DecidableEq, Repr

/-- **A block's row** (BlockRow of Johnson/Desc/First/Borders.lean; lays: the numbers of the witness's messages that the table's extractor sets there to what the statement's oracles decode to; cells: it sets the cells). -/
structure KRow where
  ins : List KItem := []
  outs : List KItem := []
  ctx : List KItem := []
  lays : List Nat := []
  laysCells : Bool := false
  known : Bool := true
  whose : String := "the frame's"
  deriving Repr

/-- The open set behind a block. -/
def stepOpen (O : List KItem) (r : KRow) : List KItem :=
  let rest := O.filter fun i => !r.ins.contains i
  rest ++ r.outs.filter fun i => !rest.contains i

/-- The open sets at all borders: one more than there are blocks. -/
def openSets : List KRow → List KItem → List (List KItem)
  | [], O => [O]
  | r :: rs, O => O :: openSets rs (stepOpen O r)

/-- A TEST ON THE TABLE: every item that a block closes or reads is open in front of it; no item that it opens is. -/
def readsOpen : List KRow → List KItem → Bool
  | [], _ => true
  | r :: rs, O => (r.ins ++ r.ctx).all O.contains && r.outs.all (fun i => !O.contains i) && readsOpen rs (stepOpen O r)

/-- What is open behind the last block. -/
def lastOpen (rs : List KRow) (O : List KItem) : List KItem := (openSets rs O).getLastD []

/-! ## 2 The first chain -/

/-- The first chain's blocks at a key file with n lookups, by their names in F_K. -/
def names₁ (n : Nat) : List String :=
  ["idx.1.send", "msg.1.send"] ++
  (List.range n).flatMap (fun l => [s!"look{l}: laid", s!"look{l}.1.caller", s!"look{l}.2.K3", s!"look{l}.3.layer", s!"look{l}: behind the batching", s!"look{l}: cleared"]) ++
  ["rng.0.rows", "rng", "batt.1.batt", "w.1.send", "seal"]

/-- A lookup's link's six rows. -/
def lookRows (l : Nat) : List KRow :=
  [ {},
    { whose := "«fast C»'s (the caller): book-keeping alone" },
    { ins := [.inRange l], outs := [.forms l "objects", .worth l "planes", .worth l "keys"], ctx := [.pinT, .pin 0, .pin 1], whose := "K3's house (part 5)" },
    { ins := [.forms l "objects", .worth l "planes", .worth l "keys"], outs := [.rows l, .kclaims l], ctx := [.pinT, .pin 0, .pin 1], whose := "«fast C»'s (the layer of rows): THE EXCHANGE" },
    {}, {} ]

/-- **The first chain's rows.** -/
def rows₁ (n : Nat) : List KRow :=
  [ { outs := [.pin 0, .srow 0], whose := "K1's house" },
    { outs := [.pin 1, .srow 1], whose := "K1's house" } ] ++
  (List.range n).flatMap lookRows ++
  [ { ins := (List.range n).map .rows ++ [.srow 1], outs := [.grows], ctx := [.pin 1], whose := "«fast C»'s (rng.0.rows)" },
    { ins := [.grows, .pin 1], lays := [1], whose := "K12's house (H2): the fresh mask that went ahead with B is ITS ROW's matter" },
    { ins := (List.range n).map .kclaims, outs := [.pile], ctx := [.pinT, .pin 0], whose := "K13's house" },
    { outs := [.pin 2, .srow 2], whose := "K1's house: THE ONE CLAIM RIDES ACROSS V's SENDING, OPEN" },
    { whose := "the chains' end's" } ]

/-- What is open in front of the first chain: THE GOAL. -/
def start₁ (n : Nat) : List KItem := [.unmarked, .pinT] ++ (List.range n).map .inRange

/-- What is open behind it: what the shared and the second chain must close. -/
def end₁ : List KItem := [.unmarked, .pinT, .pin 0, .srow 0, .pile, .pin 2, .srow 2]

/-! ## 2b Which components of the witness the first chain's items read -/

/-- The witness's messages that an item of the first chain reads. [rows l: B alone; kclaims l | pile: I alone; (Eval): V and I: BY A RUN at the honest small file: the messages that the rows in the state name.] -/
def msgsOf₁ : KItem → List Nat
  | .pin k => [k]
  | .srow k => [k]
  | .forms _ _ => [1, 0]
  | .worth _ "planes" => [1]
  | .worth _ "keys" => [0]
  | .rows _ => [1]
  | .kclaims _ => [0]
  | .grows => [1]
  | .pile => [0]
  | .claim 1 "Eval" => [2, 0]
  | .claim 1 "VIs" => [2]
  | _ => []

/-- It reads the witness's cells. -/
def cellsOf₁ : KItem → Bool
  | .pinT | .inRange _ | .worth _ "keys" | .kclaims _ | .pile | .claim 1 "VIs" => true
  | _ => false

/-- A TEST ON THE TABLE (after laysClear of Johnson/Desc/First/Borders.lean): behind a block that lays a component no open item reads it. -/
def laysClear₁ : List KRow → List KItem → Bool
  | [], _ => true
  | r :: rs, O =>
    let O' := stepOpen O r
    O'.all (fun i => (msgsOf₁ i).all (fun k => !r.lays.contains k) && !(r.laysCells && cellsOf₁ i)) && laysClear₁ rs O'

/-- A TEST ON THE TABLE: WHILE AN ITEM IS OPEN, EVERY COMPONENT THAT IT READS IS PINNED: its messages by their pins, the cells by pinT: so that what the item speaks of is fixed by the statement. -/
def readsPinned₁ : List KRow → List KItem → Bool
  | [], O => O.all fun i => (msgsOf₁ i).all (fun k => O.contains (.pin k)) && (!cellsOf₁ i || O.contains .pinT)
  | r :: rs, O => (O.all fun i => (msgsOf₁ i).all (fun k => O.contains (.pin k)) && (!cellsOf₁ i || O.contains .pinT)) && readsPinned₁ rs (stepOpen O r)

/-- A TEST ON THE TABLE: a block with rounds that closes an item has in its ctx (or closes, or opens) the pin of every component that the items which it closes and opens read. -/
def ctxPins₁ (r : KRow) : Bool :=
  let near := r.ins ++ r.outs ++ r.ctx
  (r.ins ++ r.outs).all fun i => (msgsOf₁ i).all (fun k => near.contains (.pin k)) && (!cellsOf₁ i || near.contains .pinT)

/-! ## 3 What an item says: letters -/

variable {S : Type}

/-- **What an item says**, of the chain's record (P: what was handed to the chain; S: the chain's own state), the oracles and a witness. ONE FIELD A SORT OF ITEM: each a letter here. -/
structure KMeaning (P S W : Type) where
  unmarked : P × S → Prop
  inRange : Nat → W → Prop
  near : Nat → P × S → Strs → Prop
  srow : Nat → P × S → Strs → W → Prop
  forms : Nat → String → P × S → Strs → W → Prop
  worth : Nat → String → P × S → Strs → W → Prop
  rows : Nat → P × S → Strs → W → Prop
  kclaims : Nat → P × S → Strs → W → Prop
  grows : P × S → Strs → W → Prop
  pile : P × S → Strs → W → Prop
  claim : Nat → String → P × S → Strs → W → Prop

section
variable {XI P Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)

/-- Where message k lies: a tree's number through the file, and the tenant's number in it: a letter off the plan. -/
abbrev Where : Type := Nat → Nat × Nat

/-- **An item's meaning.** inRange READS THE WITNESS ALONE: nothing of the record, nothing that was heard. -/
def KItem.holds (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) : KItem → P × S → Strs → Wit Cells Unit M → Prop
  | .unmarked => fun a _ _ => Mg.unmarked a
  | .pinT => fun a y w => PINW G a y w
  | .inRange l => fun _ _ w => Mg.inRange l w
  | .pin k => fun a y w => PIN F G (at_ k).1 (at_ k).2 a y w
  | .near k => fun a y _ => Mg.near k a y
  | .srow k => Mg.srow k
  | .forms l r => Mg.forms l r
  | .worth l x => Mg.worth l x
  | .rows l => Mg.rows l
  | .kclaims l => Mg.kclaims l
  | .grows => Mg.grows
  | .pile => Mg.pile
  | .claim c n => Mg.claim c n

/-- **The relation at a border**: every open item holds. -/
def relAt (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) (O : List KItem) (a : P × S) (y : Strs) (w : Wit Cells Unit M) : Prop :=
  ∀ i ∈ O, i.holds F G at_ Mg a y w

/-- The messages whose pin is open. -/
def pinned (O : List KItem) : List Nat := O.filterMap fun i => match i with | .pin k => some k | _ => none

/-- **The promise at a border.** shape: the book-keeping, a Bool on the state. free: NO COLLISION AT THE STORED TABLE's RECORD's SEED: a letter (the configuration's). A marked record is inside every promise.
THE STORED TABLE's DECODING IS NOT PROMISED HERE: it is the goal. -/
def onAt (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) (shape : S → Bool) (free : P × S → Strs → Prop) (O : List KItem) (a : P × S) (y : Strs) : Prop :=
  ¬ Mg.unmarked a ∨
    (shape a.2 = true ∧ ((pinned O).all fun k => hasSmp G (at_ k).1 (at_ k).2 a) = true ∧ free a y ∧
      ∀ k ∈ pinned O, NoColl F G (at_ k).1 (at_ k).2 a y)

end

/-! ## 4 Tests on the table, by evaluation -/

#eval (names₁ 2).length
#eval (rows₁ 2).length
#eval readsOpen (rows₁ 2) (start₁ 2)
#eval decide (lastOpen (rows₁ 2) (start₁ 2) = end₁)
-- controls: each is due «false»
#eval readsOpen (rows₁ 2) ([.unmarked, .pinT, .inRange 0])                       -- a goal left out
#eval readsOpen ((rows₁ 2).eraseIdx 1) (start₁ 2)                                -- B's sending struck
#eval readsOpen ((rows₁ 2).eraseIdx 5) (start₁ 2)                                -- the first layer struck
#eval decide (lastOpen ((rows₁ 2).eraseIdx 15) (start₁ 2) = end₁)                -- the ranges' test struck
#eval (openSets (rows₁ 2) (start₁ 2)).zipIdx.map fun x => (x.2, x.1.length)
#eval laysClear₁ (rows₁ 2) (start₁ 2)                                             -- due «true»
#eval readsPinned₁ (rows₁ 2) (start₁ 2)                                           -- due «true»
#eval (rows₁ 2).all ctxPins₁                                                      -- due «true»
#eval laysClear₁ ((rows₁ 2).modify 4 fun r => { r with lays := [1] }) (start₁ 2)  -- control: K3 lays B, which its own outs read: due «false»
#eval readsPinned₁ (rows₁ 2) ((start₁ 2).erase .pinT)                             -- control: the goal without pinT: due «false»
#eval ((rows₁ 2).modify 16 fun r => { r with ctx := [.pinT] }).all ctxPins₁       -- control: K13 without pin I in its ctx: due «false»
#eval readsOpen (rows₁ 3) (start₁ 3) && decide (lastOpen (rows₁ 3) (start₁ 3) = end₁)   -- general in the number of lookups: due «true»

end VerifiableInference.Desc.Key

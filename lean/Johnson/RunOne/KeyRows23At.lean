-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyRows23At.lean. THE PROMISES' LAST LETTERS ARE STRUCTURES WITH NAMED FIELDS, Free₂ | Free₃. THE RULE BEHIND THEIR FIELDS: for each block, what its decide reads and what the claim in front reads; where the two name different fields, a tie stands in the promise. Without a tie between a chain's own record and what was handed to it the law of K14's second part (no round) cannot be paid.
THE KEY FILE's SHARED AND LAST CHAIN: THE PROMISE on AND THE CLAIM L AT EACH OF THE 13 + 5 BOUNDARIES, AS FUNCTIONS OF THE STATEMENT THAT THE RULES' PIECES CARRY: at the states of the kinds' own
blocks as the key file's description seats them (the shared chain: Desc.K14.St; the last: Third.S₃; what was handed over: the instance with the first chain's last state | with both). Definitions, and two small theorems (off the image of the records the promises are false): NO LAW.
  firstAt · readers₂ | readers₃   the readers of Johnson/Desc/Key/KeyMeaning23.lean, filled: nothing is read of a state but through its own fields and the last chain's own firstOutFrom
  plan₂ | plan₃                   which of the witness's messages a statement's message is (0 I · 2 V · 3 U · 4 Omega · 5 the split's masks): the shared chain's numbers are 0 · 2 · 3 (the book-keeping Bool shape₂ holds them); the last chain's are the first chain's K₁, and nOf p for Omega (the
                                  messages at the first chain's end, off what was handed over)
  meaning₂ | meaning₃             the table's letter KMeaning at these chains: unmarked: these states bear no deferred mark · pile: the first chain's one pending row, off what was handed over · srow k: in whichever statement message k lies ·
                                  claim: claim₂ | claim₃ · the first chain's own sorts of items: False (they are open at no border here)
  open₂ | open₃                   the open sets, computed from the rows
  on₂ | R₂ | L₂ | on₃ | R₃ | L₃   on k := the table's onAt at shape₂ | shape₃ and the open pins · R k x w := every open item holds at w · L k := THERE IS SUCH A WITNESS
LETTERS LEFT: the description F (for what its blocks tell of a tree) · the reading G (code, radius, samples, the stored table's decoding) · where message k lies · K₁ (the first chain's plan's numbers) · how a witness is read (R) · enc, rad ·
coll (a collision at the record's seed: the configuration's): THE PROMISE HOLDS THE RECORD ITSELF (FreeAt, Johnson/Desc/Key/KeyOff.lean): off the image of the records it is false
at every boundary: behind «LIN point», where pinT is closed and the claims no longer name the record, that is what keeps LIN point's law meetable · a (the answers to a sample) · idx (the claim's masks' messages).
Limits. Of the promises the Bools and the decidable ties have been evaluated at the honest walk's states (by a test file that is not part of this library); the claims nowhere: an honest run shows no witness. Whether the promise behind a block follows from the promise in front and the block's yes is each block's law. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyMeaning23
import Johnson.Desc.Key.KeyOff
import Johnson.Desc.Sound.MsgAt
import Johnson.Desc.Key.KeyTies
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.RunOne.KeyHanded
import Johnson.RunOne.BorderShapes.LKFU.Shape23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)

abbrev St₂ : Type := _root_.Desc.K14.St
abbrev St₃ : Type := VerifiableInference.Desc.Third.S₃
/-- What is handed to the shared chain | to the last chain. -/
abbrev P₂ : Type := Xi × FirstState
abbrev P₃ : Type := Xi × FirstState × St₂

/-- What the last chain's start reads of the first chain's last state. -/
def firstAt (S : LinShape) (s : FirstState) : Option VerifiableInference.Desc.Third.FirstOut :=
  let f := firstOf s
  s.lin.bind fun l => VerifiableInference.Desc.Third.firstOutFrom S f.1 f.2.1 f.2.2.1 l.w l.own l.mask f.2.2.2

def evalAt (S : LinShape) (s : FirstState) : Option OnBytes.Row := (firstAt S s).bind fun f => (f.st.groups[f.own]?).bind (·.rows[0]?)

def readers₂ (S : LinShape) : KReaders23 P₂ St₂ where
  st := (·.st)
  gU := (·.loc.gU)
  gO := (·.loc.gOmega)
  own := fun _ => noId
  psi := fun a => a.2.loc.psiSh
  zeta := (·.loc.zFd)
  key := fun a => a.2.loc.key
  st₁ := fun p => (firstOf p.2).1
  eval := fun p => evalAt S p.2
  g := fun a => (firstAt S a.1.2).map (·.g)

def readers₃ (S : LinShape) : KReaders23 P₃ St₃ where
  st := (·.st)
  gU := fun _ => noId
  gO := fun _ => noId
  own := (·.loc.own)
  -- THE OWN RECORD ALONE: the border's copy, where the first block reads them
  psi := fun a => (a.2.loc.border.map (·.shared.psi)).getD []
  zeta := fun _ => []
  -- these three are read by no claim of the last chain
  key := fun a => a.1.2.2.loc.key
  st₁ := fun p => (firstOf p.2.1).1
  eval := fun p => evalAt S p.2.1
  g := fun a => a.2.loc.border.map (·.g)

/-- The shared chain's statement: message 0 is U, 2 Omega, 3 the split's masks. -/
def plan₂ (S : LinShape) : KPlan where
  lin := S
  lookups := []
  orc := fun k => if k == 3 then some 0 else if k == 4 then some 2 else if k == 5 then some 3 else none
  num := fun o => if o == 0 then some 3 else if o == 2 then some 4 else if o == 3 then some 5 else none

/-- The last chain's statement BEGINS AS THE FIRST CHAIN's LAST: its messages keep their numbers, so the plan's numbers are the first chain's K₁; Omega, taken over, is message n (n: the messages at the first chain's end). -/
def plan₃ (K₁ : KPlan) (n : Nat) : KPlan where
  lin := K₁.lin
  lookups := K₁.lookups
  orc := fun k => if k == 4 then some n else K₁.orc k
  num := fun o => if o == n then some 4 else K₁.num o

section
variable {Cells M : Type} (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

/-- Message k's sample rows, in the statement St under the plan's numbers K, hold at the witness. -/
def srowAt (K : KPlan) (St : Statement) (k : Nat) (w : Wit Cells Unit M) : Prop :=
  ∃ o x, K.orc k = some o ∧ St.oracles[o]? = some x ∧ x.sampled = true ∧ x.sampleRows.size ≠ 0 ∧ ∀ r ∈ x.sampleRows.toList, RowHolds R.same St (valOf K R w) r

def meaning₂ : KMeaning P₂ St₂ (Wit Cells Unit M) where
  unmarked := fun _ => True
  inRange := fun _ _ => False
  near := fun _ _ _ => False
  srow := fun k a _ w => if k = 0 ∨ k = 2 then srowAt R K₁ ((readers₂ S).st₁ a.1) k w else srowAt R (plan₂ S) a.2.st k w
  forms := fun _ _ _ _ _ => False
  worth := fun _ _ _ _ _ => False
  rows := fun _ _ _ _ => False
  kclaims := fun _ _ _ _ => False
  grows := fun _ _ _ => False
  -- the one claim that the batching left, read as the first chain's own table reads it: off «lin»
  pile := fun a _ w => ∃ x, (a.1.2.lin.map fun L => rowOfLinClaim L.claim) = some x ∧ TensorRowHolds R.same K₁.m (matOf K₁ R w) (mkOf K₁ R w) x
  claim := claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad

/-- The messages at the first chain's end: OFF THE LAST CHAIN's OWN RECORD: W was the last but one. -/
def nOwn (s : St₃) : Nat := s.loc.w + 2
/-- The groups | the trees there: the own group was the last; the first own tree's number counts one tree more (Omega's). -/
def gOwn (s : St₃) : Nat := s.loc.own + 1
def tOwn (s : St₃) : Nat := s.loc.firstTree - 1

def meaning₃ : KMeaning P₃ St₃ (Wit Cells Unit M) where
  unmarked := fun _ => True
  inRange := fun _ _ => False
  near := fun _ _ _ => False
  -- UNTIL THE FIRST BLOCK HAS TAKEN OMEGA OVER (the border lies) its sample rows lie in THE BORDER's OWN COPY of the shared chain's last statement; behind it in this chain's own statement
  srow := fun k a _ w => match a.2.loc.border with
    | some b => if k = 4 then srowAt R (plan₂ S) b.shared.st 4 w else srowAt R (plan₃ K₁ (nOwn a.2)) a.2.st k w
    | none => srowAt R (plan₃ K₁ (nOwn a.2)) a.2.st k w
  forms := fun _ _ _ _ _ => False
  worth := fun _ _ _ _ _ => False
  rows := fun _ _ _ _ => False
  kclaims := fun _ _ _ _ => False
  grows := fun _ _ _ => False
  pile := fun _ _ _ => False
  claim := fun c nm a y w => claim₃ (plan₃ K₁ (nOwn a.2)) R (readers₃ S) c nm a y w

end

/-- The test of «the taken trees' sources» (Johnson/Desc/Third/TakenSources.lean: takenSources), as a Bool on the state. own: the own test's block, whose declared rounds it reads. -/
def srcOk (own : Block St₃ Unit) (s : St₃) : Bool :=
  match VerifiableInference.Desc.Third.takenOf s with
  | some ts =>
    (ts.all fun x => VerifiableInference.Desc.Third.opensTaken own.rounds x.1 x.2) &&
      ((own.rounds.flatMap (·.opens)).all fun o =>
        match o.2 with
        | .own _ => true
        | .taken c n => ts.contains (c, n))
  | none => false

/-- **The last chain's book-keeping at boundary k, on its own record alone**: LKFU/Shape23.lean's shape₃ at the record's own counts · V's number is the public plan's · THE FIRST OWN TREE's NUMBER IS THE PUBLIC ONE (t₁: the trees that the first chain sends: a letter: without it the first block, which lays Omega's tree as the book's NEXT, could not earn «the own book places Omega where at_ says») · at the first border: the border's copy holds Omega as the next border will want its copy · at the
border 2: the sources' test has said yes (src: a letter; meant: srcOk at the own test's block) · AT THE LAST BORDER: THE LAST CHAIN's SHARE OF THE DESCRIPTION's LAST TEST (fin₃: every group's test has begun, every sampled message is in a group): EARNED BY
THE CHAIN's END's OWN YES, which is so spent. -/
def shapeB₃ (S : LinShape) (K₁ : KPlan) (a : Nat) (idx : List Nat) (src : St₃ → Bool) (t₁ : Nat) (k : Nat) (s : St₃) : Bool :=
  LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a (nOwn s) (gOwn s) (tOwn s) idx k s) && (K₁.orc 2 == some s.loc.w) && (s.loc.firstTree == t₁ + 1) && (k != 0 || borderB a s) && (k != 2 || src s) &&
    (k != 4 || VerifiableInference.Desc.Third.fin₃ s)

/-- **What the laws of the two sendings and of the last chain's first block will want of the letters at_ · off₂ · off₃** (public; no state): a sending lays its messages in the book's NEXT trees: so where at_ says they lie must be these. -/
structure AtOk (at_ : Where) (off₂ off₃ : Nat → Nat) (t₁ : Nat) : Prop where
  u : at_ 3 = (off₂ 0, 0)
  omega : at_ 4 = (off₂ 1, 0)
  split : at_ 5 = (off₂ 2, 0)
  omega₃ : at_ 4 = (off₃ t₁, 0)
  low : ∀ q, q < t₁ → off₃ q = q

/-- It has a member: the trees numbered through the file in the order of sending: the first chain's t₁, the shared chain's t₂, the last chain's own. In the last chain's book the first chain's trees stand first, then Omega's (the shared chain's
second), then its own. vT: V's tree. -/
theorem atOk_member (t₁ t₂ vT : Nat) :
    AtOk (fun k => if k = 0 then (0, 0) else if k = 2 then (vT, 0) else (t₁ + (k - 3), 0)) (fun q => t₁ + q)
      (fun q => if q < t₁ then q else if q = t₁ then t₁ + 1 else t₁ + t₂ + (q - t₁ - 1)) t₁ :=
  ⟨rfl, rfl, rfl, by simp, fun q hq => by simp [hq]⟩

/-- What is open at boundary k of the shared | the last chain. -/
def open₂ (k : Nat) : List KItem := ((openSets rows₂ seam)[k]?).getD []
def open₃ (k : Nat) : List KItem := ((openSets rows₃ end₂)[k]?).getD []

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **The promise's last letter at boundary k of the shared chain.** -/
structure Free₂ (k : Nat) (z : P₂ × St₂) (y : Strs) : Prop where
  /-- THE RECORD IS THERE and the stored table has no collision at its seed (so off the image of the records the promise is false) -/
  record : FreeAt G₂ coll z y
  /-- OF WHAT WAS HANDED (no block of this chain turns it): the first chain's last book-keeping, whole -/
  last : last₁ z.1.2 = true
  /-- … the row (Eval) as it lies there is the claim's -/
  eval : EvalIs S z.1.2
  /-- … its book places I and V where at_ says -/
  placed₁ : Placed K₁.orc (fun o => z.1.2.d.book.place[o]?) id at_ [0, 2]
  /-- … its pinned messages' sample rows and its own group's open row lie on their own tables -/
  in₁ : HandedIn K₁.orc z.1.2
  /-- … its statement is in order -/
  order₁ : Means.InOrder z.1.2.d.st
  /-- THE OWN RECORD AGAINST WHAT WAS HANDED: the own copy of the key is the instance's («RecRow» and (rec_gamma) read the copy; pinT the record off the instance) -/
  key : z.2.loc.key = z.1.1.key
  /-- … the codes are the first chain's («DotU» | «DotOm» read V's layout at these; the row (Eval) was made at those) -/
  codes : z.2.st.codes = z.1.2.d.st.codes
  /-- WITHIN THE OWN RECORD: behind o_u's sending the copy of its layout is the layout of the codes and the shape ((rec_gamma) · LOC · SPLIT read the copy; «RecRow» · «NearU» · «Fold» the codes and the shape) -/
  lay : 3 ≤ k → z.2.loc.oU.lay = vectorLay z.2.st.codes S.fold.u S.fold.rowsHigh
  /-- THE LETTERS: what PIN k pins is the witness's message k -/
  arr : ArrOk G₂ at_ [0, 2, 3, 4, 5]
  /-- … and the table that the rows read of message k is the table that PIN k pins -/
  reads : ReadsPinned G₂ at_ R [0, 2, 3, 4, 5]
  /-- … the own book places the chain's own pinned messages where at_ says -/
  placed : Placed (plan₂ S).orc (fun o => z.2.book.place[o]?) off₂ at_ ((pinned (open₂ k)).filter (3 ≤ ·))
  /-- THE ROWS' CONTENT: the chain's own pinned messages' sample rows, and the two groups' open rows, lie on their own tables -/
  samples : ∀ k' ∈ (pinned (open₂ k)).filter (3 ≤ ·), ∀ o, (plan₂ S).orc k' = some o → SampleIn z.2.st o
  rowsIn : 2 ≤ k → OpenIn z.2.st z.2.loc.gU ∧ OpenIn z.2.st z.2.loc.gOmega
  /-- THE OWN STATEMENT IS IN ORDER (samples and rowsIn follow from it: sampleIn_of_order | openIn_of_order) -/
  order : Means.InOrder z.2.st
  /-- THREE TIES TO THE PUBLIC SHAPE (wanted by the last chain's files for rows 2.8 | 2.3: the library's laws on what (fold)'s and (rec_gamma)'s rows mean want them): behind «LIN point»: the public shape's conditions at the own codes (TO BE EARNED AT 2.1, by that block's own test; no law pays it yet) -/
  linOk : 2 ≤ k → OnBytes.linOk z.2.st.codes S = true
  /-- … behind o_u's sending: message 0 has the folded row's shape (TO BE EARNED AT 2.2, the sending; no law pays it yet) -/
  seatU : 3 ≤ k → (z.2.st.oracles[0]?).any (·.shape == S.fold.u) = true
  /-- … behind o_omega's sending: message 2 has Omega's shape (TO BE EARNED AT 2.5, the sending; no law pays it yet) -/
  seatOmega : 6 ≤ k → (z.2.st.oracles[2]?).any (·.shape == S.omega) = true
  /-- EVERY LEAF IS SHOWN AT EVERY OPEN PIN (TO BE EARNED at the sendings, a fact of the piece; it rides wherever the word at the seat stays) -/
  shown : ∀ j ∈ pinned (open₂ k), ShownAt F at_ j y
  /-- ON THE INSTANCE: the key fits the shape (earned at the very first border from the instance's own test; for K14's files' promise on the key) -/
  fits : z.1.1.key.fits S.fold.index = true
  /-- OF WHAT WAS HANDED: V's test's first mask lies in V's tree, the next part (TO BE EARNED AT 1.17) -/
  mask₁ : ∀ o, K₁.orc 2 = some o → MaskWith (fun i => z.1.2.d.book.place[i]?) o (o + 1)
  /-- behind o_u's sending: its test's first mask lies in its tree, the next part (TO BE EARNED AT 2.2; every later block only appends to the book) -/
  maskU : 3 ≤ k → MaskWith (fun i => z.2.book.place[i]?) 0 1

/-- **The same of the last chain: ON ITS OWN RECORD ALONE** (but for the stored table's record, which is the instance's). -/
structure Free₃ (k : Nat) (z : P₃ × St₃) (y : Strs) : Prop where
  record : FreeAt G₃ coll z y
  arr : ArrOk G₃ at_ [0, 2, 4]
  reads : ReadsPinned G₃ at_ R [0, 2, 4]
  /-- up to the own test: the own book places I and V where at_ says -/
  placed : k ≤ 2 → Placed K₁.orc (fun o => z.2.book.place[o]?) off₃ at_ [0, 2]
  /-- while the border lies: its copy of the shared chain's book places Omega where at_ says -/
  omega₀ : k = 0 → ∃ b, z.2.loc.border = some b ∧ Placed (fun _ => some b.shared.omega) (fun o => b.shared.book.place[o]?) off₂ at_ [4]
  /-- behind the first block: the own book does -/
  omega : 1 ≤ k → k ≤ 2 → Placed (fun _ => some z.2.loc.omega) (fun o => z.2.book.place[o]?) off₃ at_ [4]
  /-- THE ROWS' CONTENT: while the border lies: Omega's sample rows in the border's copy -/
  in₀ : k = 0 → ∃ b, z.2.loc.border = some b ∧ SampleIn b.shared.st b.shared.omega
  /-- up to the own test: I's and V's sample rows and the own group's open rows, in the own statement -/
  inOwn : k ≤ 2 → (∀ k' ∈ [0, 2], ∀ o, K₁.orc k' = some o → SampleIn z.2.st o) ∧ OpenIn z.2.st z.2.loc.own
  /-- behind the first block: Omega's copy's -/
  inOmega : 1 ≤ k → k ≤ 2 → SampleIn z.2.st z.2.loc.omega
  /-- THE OWN STATEMENT IS IN ORDER; while the border lies, its copy of the shared statement too -/
  order : Means.InOrder z.2.st
  order₀ : k = 0 → ∃ b, z.2.loc.border = some b ∧ Means.InOrder b.shared.st
  shown : ∀ j ∈ pinned (open₃ k), ShownAt F at_ j y
  /-- V's test's first mask lies in V's tree, the next part (the own book begins as the first chain's; every block only appends to it) -/
  maskW : MaskWith (fun i => z.2.book.place[i]?) z.2.loc.w (z.2.loc.w + 1)
  /-- THREE TIES TO THE PUBLIC SHAPE AT THE FIRST BORDER (the library's law on what (Dot)'s row means wants them): the shape's conditions at the own codes; W has its shape (both: the chain's start's own tests) -/
  lin₀ : k = 0 → OnBytes.linOk z.2.st.codes S = true
  seatW : k = 0 → (z.2.st.oracles[z.2.loc.w]?).any (·.shape == S.w) = true
  /-- … and in the border's copy Omega has its shape (from the shared chain's last promise) -/
  seatOmega₀ : k = 0 → ∀ b, z.2.loc.border = some b → (b.shared.st.oracles[b.shared.omega]?).any (·.shape == S.omega) = true

/-- **The promise at boundary k of the shared chain.** -/
def on₂ (k : Nat) (x : (P₂ × St₂) × Fr₂.E.Str) : Prop :=
  onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k) (open₂ k) x.1 (strsOf Fr₂ x.2)

/-- **The relation there**, with its witness: every open item holds. -/
def R₂ (k : Nat) (x : (P₂ × St₂) × Fr₂.E.Str) (w : Wit Cells Unit M) : Prop :=
  relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ k) x.1 (strsOf Fr₂ x.2) w

/-- **The claim there**: there is a witness at which every open item holds. -/
def L₂ (k : Nat) (x : (P₂ × St₂) × Fr₂.E.Str) : Prop := ∃ w, R₂ F Fr₂ G₂ at_ S K₁ R enc rad k x w

/-- **The promise at boundary k of the last chain.** -/
def on₃ (k : Nat) (x : (P₃ × St₃) × Fr₃.E.Str) : Prop :=
  onAt F G₃ at_ (meaning₃ S K₁ R) (shapeB₃ S K₁ a idx src t₁ k) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ k) (open₃ k) x.1 (strsOf Fr₃ x.2)

/-- **The relation there**, with its witness. -/
def R₃ (k : Nat) (x : (P₃ × St₃) × Fr₃.E.Str) (w : Wit Cells Unit M) : Prop :=
  relAt F G₃ at_ (meaning₃ S K₁ R) (open₃ k) x.1 (strsOf Fr₃ x.2) w

/-- **The claim there.** -/
def L₃ (k : Nat) (x : (P₃ × St₃) × Fr₃.E.Str) : Prop := ∃ w, R₃ F Fr₃ G₃ at_ S K₁ R k x w

end

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **Off the image of the records the promise is false at every boundary of the shared chain.** -/
theorem off₂_on (k : Nat) (x : (P₂ × St₂) × Fr₂.E.Str) (h : G₂.recOf x.1 = none) : ¬ on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k x := by
  intro ho
  cases ho with
  | inl hn => exact hn trivial
  | inr hr => exact not_free_off G₂ coll x.1 _ h hr.2.2.1.record

/-- **The last promise holds the last chain's share of the description's last test.** -/
theorem fin₃_of_on₃ (x : (P₃ × St₃) × Fr₃.E.Str) (h : on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 4 x) : VerifiableInference.Desc.Third.fin₃ x.1.2 = true := by
  cases h with
  | inl hn => exact absurd trivial hn
  | inr hr =>
    have hs : shapeB₃ S K₁ a idx src t₁ 4 x.1.2 = true := hr.1
    simp only [shapeB₃, Bool.and_eq_true] at hs
    simpa using hs.2

/-- And of the last. -/
theorem off₃_on (k : Nat) (x : (P₃ × St₃) × Fr₃.E.Str) (h : G₃.recOf x.1 = none) : ¬ on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k x := by
  intro ho
  cases ho with
  | inl hn => exact hn trivial
  | inr hr => exact not_free_off G₃ coll x.1 _ h hr.2.2.1.record

end

/-! ## Tests, by evaluation -/

#eval (List.range 13).map fun k => (open₂ k).length
#eval (List.range 5).map fun k => (open₃ k).length
#eval decide (open₂ 0 = seam) && decide (open₂ 12 = end₂) && decide (open₃ 0 = end₂) && decide (open₃ 4 = [.unmarked])
-- no item of the first chain's own sorts (whose meaning is «False» here) is open at any of the eighteen boundaries: due «true»
#eval ((List.range 13).flatMap open₂ ++ (List.range 5).flatMap open₃).all fun i => match i with
  | .inRange _ | .near _ | .forms _ _ | .worth _ _ | .rows _ | .kclaims _ | .grows => false
  | _ => true
-- the pile is open at the shared chain's first two boundaries alone, and nowhere on the last: due «true»
#eval ((List.range 13).filter fun k => (open₂ k).contains .pile) == [0, 1] && (List.range 5).all fun k => !(open₃ k).contains .pile

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.atOk_member
#print axioms Johnson.RunOne.KeyRows23.fin₃_of_on₃
#print axioms Johnson.RunOne.KeyRows23.off₂_on
#print axioms Johnson.RunOne.KeyRows23.off₃_on

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PartM3.lean: kind K13's three sub-protocols of the members' batching
(`frontB`, `claimCombinationBlock`, `quietB`, Johnson/Desc/K13/Kind.lean) AT EVERY LENS: when their decisions
accept, and what the shape of the part behind is. Definitions with code, and statements with their
proofs.

The kind's sub-protocols are written over a lens X into a state of any type T: they read the
structure `Part` that `X.get?` yields (the front: behind `X.enter`) and write a `Part` back with
`X.set`. So each is one text on the `Part`; the laws are stated of these texts, once; a lens is an
instance. Johnson/Desc/K13/Honest/ShapeAll.lean has the law at the first chain's state of the proof
file's IOP and its lens `atS`, for the three joined (`atM3_returns`). What is called here is general
in the plain texts' arguments already: `batt_returns_fit` (AcceptsFit.lean), the library's
`batt_ok`, `takeMasks_msgs` (ShapeStep.lean), `takeMasks_takeL` (ShapeAll.lean), `rowSh_rowOf`
(ClaimShape.lean), `takeMasks_returns` and `leftAtC_iff` (Room.lean), `quiet_returns`,
`frontB_accepts` and `quietB_accepts` (SubProtocols.lean), and the library's `takeMasks_same` and
`front_is`. Three equations are stated at a state and are called at a state that is made of the part
(`stateOfPart3`), which stands in no statement: `roomSh_eq`, `fitSh_eq` (Shape.lean) and
`ledgerSh_shOf` (ShapeAll.lean); `formSh_eq` is stated at a pile and called at the part's.
The form of the laws: premises on the part's shape and the step's own test on rounds: then the texts
return, whatever the field elements in the part and in the rounds, and the shape behind is a
function with code of the shape in front.
Main names:
  `frontTest`, `battPart`, `quietPart`: the three texts on the part. `frontB_is_part`,
    `battB_is_part`, `quietB_is_part`: **at every lens each sub-protocol is its text between `get?`
    and `set`.**
  `partSh3`: the part's shape: an `Sh` (ShapeDefs.lean): "nothing is batched yet" for the flag
    `atFin`; "no count is owed" for `quiet`.
  `ready_of_partShape`: where the nine tests `readySh` accept at the part's shape, the nine premises
    hold of the part's fields; a tenth conjunct: the index masks' message has a ledger.
  `m3Part_returns`: **the law**: the nine tests accept at the part's shape, the rounds pass
    `roundsFit` at `battRounds P`: then the three texts return in a row; the shape behind is
    `updSh`; the claim's row's shape is `claimSh` at the pile's rows' shapes and the slots that the
    shape foretells; W's message is the plan's; the other fields stay.
  `frontB_returns_at`, `battB_returns_at`, `quietB_returns_at`: the three laws at any lens, one
    sub-protocol each. No law on the lens is asked.
  `m3_returns_at`: **the three in a row at a lens that reads back what is written**: the premise hX
    is that of the library's `lensLaw_of_same` (Johnson/Desc/K13/Law/GoodAny.lean): where a part
    that keeps `heard`, `indexMasks` and `pile` and owes nothing is written, that part is read. The
    key file's `batchLens` has it (`lens_get_set_same`, Johnson/Desc/Key/KeyLensLaws.lean). The
    proof file's `atS` has it NOT (it writes back the statement alone of the part's ground): there
    `atM3_returns` is the law.
  `m3_returns_law`: **the three in a row under the library's two laws on a lens**: `LensLaw`
    (Law/GoodAny.lean) and `LensSt` (Johnson/Desc/K13/Keeps.lean): BOTH LENSES HAVE BOTH. It is said
    of the part that is READ behind: its shape is the update's, its claim is made of a row of the
    foretold shape; of that part's `msg` and `ids` nothing is said: neither law hands them back.

What is not claimed. The converse of a law. That the tests accept at any state of a run. The field
`decide` alone is treated: not `Block.step`, not the test on the plan; how a joined sub-protocol
cuts its rounds among the three is not spoken of: the three decisions are taken in a row, the middle
one on the rounds. That a number in a shape at a state of a run is made of no sent value and of no
coin. "Accepts" is `Block.decide`'s answer `.ok` and no more. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeAll
import Johnson.Desc.K13.Law.GoodAny
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.K13.Law

/-! ## The three texts on the part -/

/-- The text of `frontB` on the part that stands behind `enter`. -/
def frontTest (P : Where) (p : Part) : Ans Unit :=
  front p.d.st P.lin p.indexMasks p.pile P.reply p.heard P.rows

/-- The text of `claimCombinationBlock` on the part. -/
def battPart (P : Where) (p : Part) (rs : List Fmt.RoundView) : Ans Part := do
  need "K13.batched-once" p.lin.isNone
  let o ← batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs
  pure { p with owed := none, lin := some { claim := memberClaim o.1 }, d := o.2 }

/-- The text of `quietB` on the part. -/
def quietPart (P : Where) (p : Part) : Ans Part := do
  need "K13.claim-laid" p.lin.isSome
  let msg ← quiet p.d.st.codes P.lin
  pure { p with msg := msg }

section AnyLens
variable {T Cl : Type} (X : Lens T) (P : Where)

/-- At every lens `frontB` is its text behind `enter` and `get?`; it hands on the state behind
`enter`. -/
theorem frontB_is_part (t : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (frontB (Cl := Cl) X P).decide t rs gs =
      (there "K13.comes-to-the-end-once" (X.enter t)).bind fun t₁ =>
        (X.part t₁).bind fun p => (frontTest P p).map fun _ => t₁ := by
  show (do
    let t₁ ← there "K13.comes-to-the-end-once" (X.enter t)
    let s ← X.part t₁
    front s.d.st P.lin s.indexMasks s.pile P.reply s.heard P.rows
    pure t₁ : Ans T) = _
  cases there "K13.comes-to-the-end-once" (X.enter t) with
  | error e => rfl
  | ok t₁ =>
    show (do
      let s ← X.part t₁
      front s.d.st P.lin s.indexMasks s.pile P.reply s.heard P.rows
      pure t₁ : Ans T) = (X.part t₁).bind fun p => (frontTest P p).map fun _ => t₁
    cases X.part t₁ with
    | error e => rfl
    | ok p =>
      show (do
        front p.d.st P.lin p.indexMasks p.pile P.reply p.heard P.rows
        pure t₁ : Ans T) = (frontTest P p).map fun _ => t₁
      unfold frontTest
      cases front p.d.st P.lin p.indexMasks p.pile P.reply p.heard P.rows <;> rfl

/-- At every lens `claimCombinationBlock` is its text between `get?` and `set`. -/
theorem battB_is_part (t : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (claimCombinationBlock (Cl := Cl) X P).decide t rs gs =
      (X.part t).bind fun p => (battPart P p rs).map (X.set t) := by
  show (do
    let s ← X.part t
    need "K13.batched-once" s.lin.isNone
    let o ← batt s.owed P.lin.kCol P.rows s.pile s.indexMasks s.d rs
    pure (X.set t { s with owed := none, lin := some { claim := memberClaim o.1 }, d := o.2 }) :
      Ans T) = _
  cases X.part t with
  | error e => rfl
  | ok p =>
    show (do
      need "K13.batched-once" p.lin.isNone
      let o ← batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs
      pure (X.set t { p with owed := none, lin := some { claim := memberClaim o.1 }, d := o.2 }) :
        Ans T) = (battPart P p rs).map (X.set t)
    unfold battPart
    cases need "K13.batched-once" p.lin.isNone with
    | error e => rfl
    | ok u =>
      show (do
        let o ← batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs
        pure (X.set t { p with owed := none, lin := some { claim := memberClaim o.1 }, d := o.2 })
          : Ans T) =
        (do
          let o ← batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs
          pure { p with owed := none, lin := some { claim := memberClaim o.1 }, d := o.2 } :
            Ans Part).map (X.set t)
      cases batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d rs <;> rfl

/-- At every lens `quietB` is its text between `get?` and `set`. -/
theorem quietB_is_part (t : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (quietB (Cl := Cl) X P).decide t rs gs =
      (X.part t).bind fun p => (quietPart P p).map (X.set t) := by
  show (do
    let s ← X.part t
    need "K13.claim-laid" s.lin.isSome
    let msg ← quiet s.d.st.codes P.lin
    pure (X.set t { s with msg := msg }) : Ans T) = _
  cases X.part t with
  | error e => rfl
  | ok p =>
    show (do
      need "K13.claim-laid" p.lin.isSome
      let msg ← quiet p.d.st.codes P.lin
      pure (X.set t { p with msg := msg }) : Ans T) = (quietPart P p).map (X.set t)
    unfold quietPart
    cases need "K13.claim-laid" p.lin.isSome with
    | error e => rfl
    | ok u =>
      show (do
        let msg ← quiet p.d.st.codes P.lin
        pure (X.set t { p with msg := msg }) : Ans T) =
        (do
          let msg ← quiet p.d.st.codes P.lin
          pure { p with msg := msg } : Ans Part).map (X.set t)
      cases quiet p.d.st.codes P.lin <;> rfl

end AnyLens

/-! ## The part's shape; the nine premises -/

/-- **The part's shape.** -/
def partSh3 (p : Part) : Sh :=
  ⟨p.lin.isNone, p.heard.isSome, p.owed.isNone, p.indexMasks, p.pile.map rowSh, p.d.st.codes,
    msgsOf p.d.st⟩

/-- A state of the proof file's first chain with the part's statement, pile, number of the index
masks' message and reply laid in: a device of the proofs below, through which the equations of
Shape.lean are called; it stands in no statement. -/
def stateOfPart3 (p : Part) : S :=
  { S.blank with
    st := p.d.st, out := { indexMasks := p.indexMasks, pending := p.pile, reply := p.heard } }

/-- **Where the nine tests accept at the part's shape, the nine premises hold of the part's
fields**; and, a tenth conjunct, the index masks' message has a ledger. -/
theorem ready_of_partShape {P : Where} {p : Part} (h : readySh P (partSh3 p) = true) :
    ∃ (t : List ℕ × St) (msg : Array OracleNotice) (l : Ledger),
      p.lin.isNone = true ∧ (!P.reply || p.heard.isSome) = true ∧ p.pile.length = P.rows ∧
      memberRowsFit p.d.st P.lin p.indexMasks p.pile = true ∧ p.owed.isNone = true ∧
      Batt.fits P.lin.kCol p.pile = true ∧
      takeMasksP p.d p.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linOk p.d.st.codes P.lin = true ∧ linMessageW P.lin = some msg ∧
      (p.d.st.oracles[p.indexMasks]?).bind (·.ledger) = some l := by
  unfold readySh at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  obtain ⟨msg, hm⟩ := Option.isSome_iff_exists.1 h9
  have h7' : roomSh (shOf (stateOfPart3 p)) (Batt.masksOf P.lin.kCol) = true := h7
  rw [roomSh_eq] at h7'
  have hleft : LeftAt p.d.st p.indexMasks (Batt.masksOf P.lin.kCol) := (leftAtC_iff _ _ _).1 h7'
  obtain ⟨t, ht⟩ := takeMasks_returns (d := p.d) hleft
  obtain ⟨x, l, hx, hl, _, _⟩ := hleft
  have h4' : fitSh P.lin (shOf (stateOfPart3 p)) = true := h4
  rw [fitSh_eq] at h4'
  have h6' : formSh P.lin.kCol (p.pile.map rowSh) = true := h6
  rw [formSh_eq] at h6'
  have h3' : (p.pile.map rowSh).length = P.rows := eq_of_beq h3
  rw [List.length_map] at h3'
  exact ⟨t, msg, l, h1, h2, h3', h4', h5, h6', ht, h8, hm, by rw [hx]; exact hl⟩

/-! ## The law on the part -/

/-- **THE LAW**: the nine tests accept at the part's shape, the rounds pass the step's own test on
rounds: then the three texts return in a row, whatever elements the part and the rounds hold. p₁:
the part behind the batching; p₂: behind the third text. The shape behind is the update's; the
claim's row's shape is `claimSh` at the pile's rows' shapes and the slots that the shape foretells;
W's message is the plan's; the other fields stay. -/
theorem m3Part_returns {P : Where} {p : Part} (h : readySh P (partSh3 p) = true)
    (rs : List Fmt.RoundView) (hr : roundsFit (battRounds P) rs = true) :
    ∃ (p₁ p₂ : Part) (row : TensorRow), frontTest P p = .ok () ∧
      battPart P p (rs.map noDigest) = .ok p₁ ∧ quietPart P p₁ = .ok p₂ ∧
      partSh3 p₂ = updSh P (partSh3 p) ∧ p₂.lin = some { claim := memberClaim row } ∧
      rowSh row = claimSh P.lin.kCol (partSh3 p).pile
        (freshSh (Batt.masksOf P.lin.kCol) (partSh3 p)) ∧
      some p₂.msg = linMessageW P.lin ∧ p₁.owed = none ∧ p₁.heard = p.heard ∧
      p₁.indexMasks = p.indexMasks ∧ p₁.pile = p.pile ∧ p₂.owed = none ∧ p₂.heard = p.heard ∧
      p₂.indexMasks = p.indexMasks ∧ p₂.pile = p.pile ∧ p₂.ids = p.ids := by
  obtain ⟨t, msg, l, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := ready_of_partShape h
  obtain ⟨row₀, hb⟩ := batt_returns_fit P a5 a6 a3 a7 rs hr
  obtain ⟨_, _, x, t', hd, o, _, _, _, _, _, b4, _, b6, _, b8⟩ := batt_ok hb
  obtain rfl : t = t' := Option.some.inj (a7.symm.trans b4)
  have hrow : row₀ = Batt.rowOf p.pile o := congrArg Prod.fst b8
  have hfront : frontTest P p = .ok () := by
    unfold frontTest
    simp only [front_is, Law.bind_ok, Law.need_ok]
    exact ⟨(), a2, (), beq_iff_eq.2 a3, a4⟩
  have hbatt : battPart P p (rs.map noDigest) =
      .ok { p with owed := none, lin := some { claim := memberClaim row₀ }, d := t.2 } := by
    simp only [battPart, Law.bind_ok, Law.need_ok, Law.pure_ok]
    exact ⟨(), a1, _, hb, rfl⟩
  have ecodes : t.2.st.codes = p.d.st.codes := (takeMasks_same a7).1
  have hquiet :
      quietPart P { p with owed := none, lin := some { claim := memberClaim row₀ }, d := t.2 } =
      .ok { p with owed := none, lin := some { claim := memberClaim row₀ }, d := t.2, msg := msg }
      := by
    simp only [quietPart, Law.bind_ok, Law.need_ok, Law.pure_ok]
    exact ⟨(), rfl, msg, quiet_returns (by rw [ecodes]; exact a8) a9, rfl⟩
  refine ⟨_, _, row₀, hfront, hbatt, hquiet, ?_, rfl, ?_, a9.symm, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩
  · show Sh.mk false p.heard.isSome true p.indexMasks (p.pile.map rowSh) t.2.st.codes
      (msgsOf t.2.st) = _
    rw [ecodes, takeMasks_msgs a7]
    rfl
  · rw [hrow, rowSh_rowOf a6 b6, takeMasks_takeL a10 a7]
    have e : ledgerSh (partSh3 p) = some l := by
      have q := ledgerSh_shOf (stateOfPart3 p)
      exact q.trans a10
    unfold freshSh
    rw [e]
    rfl

/-! ## At any lens -/

section AnyLens
variable {T Cl : Type} (X : Lens T) (P : Where)

/-- The front, at any lens. -/
theorem frontB_returns_at {t t₁ : T} {p : Part} (he : X.enter t = some t₁)
    (hp : X.get? t₁ = some p) (h : readySh P (partSh3 p) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) : (frontB (Cl := Cl) X P).decide t rs gs = .ok t₁ := by
  obtain ⟨_, _, _, _, a2, a3, a4, _⟩ := ready_of_partShape h
  exact frontB_accepts X P he hp a2 a3 a4 rs gs

/-- From a return of the batching's text to the decision's acceptance, at any lens. -/
theorem battB_of_part {t : T} {p p₁ : Part} {rs : List Fmt.RoundView} (hp : X.get? t = some p)
    (h : battPart P p rs = .ok p₁) (gs : List (List (Nat × List UInt64))) :
    (claimCombinationBlock (Cl := Cl) X P).decide t rs gs = .ok (X.set t p₁) := by
  have e : X.part t = .ok p := by
    unfold Lens.part
    rw [hp]
    rfl
  rw [battB_is_part, e]
  show (battPart P p rs).map (X.set t) = _
  rw [h]
  rfl

/-- The like of the third text. -/
theorem quietB_of_part {t : T} {p p₂ : Part} (hp : X.get? t = some p)
    (h : quietPart P p = .ok p₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (quietB (Cl := Cl) X P).decide t rs gs = .ok (X.set t p₂) := by
  have e : X.part t = .ok p := by
    unfold Lens.part
    rw [hp]
    rfl
  rw [quietB_is_part, e]
  show (quietPart P p).map (X.set t) = _
  rw [h]
  rfl

/-- The batching, at any lens: on all rounds that pass the step's own test on rounds. -/
theorem battB_returns_at {t : T} {p : Part} (hp : X.get? t = some p)
    (h : readySh P (partSh3 p) = true) (rs : List Fmt.RoundView)
    (hr : roundsFit (battRounds P) rs = true) (gs : List (List (Nat × List UInt64))) :
    ∃ p₁, (claimCombinationBlock (Cl := Cl) X P).decide t (rs.map noDigest) gs = .ok (X.set t p₁) ∧
      battPart P p (rs.map noDigest) = .ok p₁ := by
  obtain ⟨p₁, _, _, _, hb, _⟩ := m3Part_returns h rs hr
  exact ⟨p₁, battB_of_part X P hp hb gs, hb⟩

/-- The third sub-protocol, at any lens: a claim is laid; the shape is lawful at the part's codes;
the plan has W's message. -/
theorem quietB_returns_at {t : T} {p : Part} {msg : Array OracleNotice} (hp : X.get? t = some p)
    (hl : p.lin.isSome = true) (h1 : linOk p.d.st.codes P.lin = true)
    (h2 : linMessageW P.lin = some msg) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (quietB (Cl := Cl) X P).decide t rs gs = .ok (X.set t { p with msg := msg }) :=
  quietB_accepts X P hp hl (quiet_returns h1 h2) rs gs

/-- **THE THREE IN A ROW, at a lens that reads back what is written** (hX: the premise of the
library's `lensLaw_of_same`). rs₀, rs₂: whatever rounds the first and the third are handed: they
read none. The state behind is `X.set` twice; the part that is laid last has the shape of the
update. -/
theorem m3_returns_at
    (hX : ∀ t p p', X.get? t = some p → p'.heard = p.heard → p'.indexMasks = p.indexMasks →
      p'.pile = p.pile → p'.owed = none → X.get? (X.set t p') = some p')
    {t t₁ : T} {p : Part} (he : X.enter t = some t₁) (hp : X.get? t₁ = some p)
    (h : readySh P (partSh3 p) = true) (rs : List Fmt.RoundView)
    (hr : roundsFit (battRounds P) rs = true) (rs₀ rs₂ : List Fmt.RoundView)
    (gs₀ gs₁ gs₂ : List (List (Nat × List UInt64))) :
    ∃ (p₁ p₂ : Part) (row : TensorRow),
      (((frontB (Cl := Cl) X P).decide t rs₀ gs₀).bind fun a =>
        (claimCombinationBlock (Cl := Cl) X P).decide a (rs.map noDigest) gs₁).bind (fun a =>
                        (quietB (Cl := Cl) X P).decide a rs₂ gs₂) = .ok (X.set (X.set t₁ p₁) p₂) ∧
      X.get? (X.set (X.set t₁ p₁) p₂) = some p₂ ∧ partSh3 p₂ = updSh P (partSh3 p) ∧
      p₂.lin = some { claim := memberClaim row } ∧
      rowSh row = claimSh P.lin.kCol (partSh3 p).pile
        (freshSh (Batt.masksOf P.lin.kCol) (partSh3 p)) ∧
      some p₂.msg = linMessageW P.lin := by
  obtain ⟨p₁, p₂, row, _, hb, hq, e1, e2, e3, e4, c1, c2, c3, c4, d1, d2, d3, d4, _⟩ :=
    m3Part_returns h rs hr
  have g1 : X.get? (X.set t₁ p₁) = some p₁ := hX t₁ p p₁ hp c2 c3 c4 c1
  have g2 : X.get? (X.set (X.set t₁ p₁) p₂) = some p₂ :=
    hX _ p₁ p₂ g1 (d2.trans c2.symm) (d3.trans c3.symm) (d4.trans c4.symm) d1
  refine ⟨p₁, p₂, row, ?_, g2, e1, e2, e3, e4⟩
  rw [frontB_returns_at X P he hp h rs₀ gs₀]
  show ((claimCombinationBlock (Cl := Cl) X P).decide t₁ (rs.map noDigest) gs₁).bind _ = _
  rw [battB_of_part X P hp hb gs₁]
  exact quietB_of_part X P g1 hq rs₂ gs₂

/-- **THE THREE IN A ROW, UNDER THE LIBRARY's TWO LAWS ON A LENS**: `LensLaw`
(Johnson/Desc/K13/Law/GoodAny.lean) and `LensSt` (Johnson/Desc/K13/Keeps.lean), which the proof
file's `atS` and the key file's `batchLens` both have. It is said of the part q that is READ behind:
its shape is the update's; its claim is made of a row of the foretold shape. Of q's `msg` and `ids`
nothing is said: neither law hands them back. -/
theorem m3_returns_law {st : T → Statement} (hL : LensLaw X) (hS : LensSt X st) {t t₁ : T}
    {p : Part} (he : X.enter t = some t₁) (hp : X.get? t₁ = some p)
    (h : readySh P (partSh3 p) = true) (rs : List Fmt.RoundView)
    (hr : roundsFit (battRounds P) rs = true) (rs₀ rs₂ : List Fmt.RoundView)
    (gs₀ gs₁ gs₂ : List (List (Nat × List UInt64))) :
    ∃ (t' : T) (q : Part) (row : TensorRow),
      (((frontB (Cl := Cl) X P).decide t rs₀ gs₀).bind fun a =>
        (claimCombinationBlock (Cl := Cl) X P).decide a (rs.map noDigest) gs₁).bind (fun a =>
                        (quietB (Cl := Cl) X P).decide a rs₂ gs₂) = .ok t' ∧
      X.get? t' = some q ∧ partSh3 q = updSh P (partSh3 p) ∧
      q.lin = some { claim := memberClaim row } ∧
      rowSh row = claimSh P.lin.kCol (partSh3 p).pile
        (freshSh (Batt.masksOf P.lin.kCol) (partSh3 p)) := by
  obtain ⟨_, msg, _, _, _, _, _, _, _, _, a8, a9, _⟩ := ready_of_partShape h
  obtain ⟨p₁, p₂, row, _, hb, hq, e1, e2, e3, _, c1, c2, c3, c4, _⟩ := m3Part_returns h rs hr
  -- what the third text has done on the part
  have hq' := hq
  simp only [quietPart, Law.bind_ok, Law.need_ok, Law.pure_ok] at hq'
  obtain ⟨_, hl₁, m₂, _, rfl⟩ := hq'
  -- the part that is read behind the batching
  obtain ⟨q₁, g1, f1, f2, f3, f4, f5⟩ := hL t₁ p p₁ hp c2 c3 c4 c1
  have s1 : q₁.d.st = p₁.d.st := (hS.get _ _ g1).trans (hS.set t₁ p p₁ hp)
  have ec : p₁.d.st.codes = p.d.st.codes := congrArg Sh.codes e1
  have hcodes : linOk q₁.d.st.codes P.lin = true := by
    rw [s1, ec]
    exact a8
  have k3 := quietB_returns_at (Cl := Cl) X P g1 (by rw [f5]; exact hl₁) hcodes a9 rs₂ gs₂
  -- the part that is read behind the third
  obtain ⟨q, g2, u1, u2, u3, u4, u5⟩ :=
    hL (X.set t₁ p₁) q₁ { q₁ with msg := msg } g1 rfl rfl rfl f4
  have s2 : q.d.st = p₁.d.st :=
    ((hS.get _ _ g2).trans (hS.set (X.set t₁ p₁) q₁ { q₁ with msg := msg } g1)).trans s1
  have v5 : q.lin = p₁.lin := u5.trans f5
  have v1 : q.heard = p₁.heard := u1.trans f1
  have v2 : q.indexMasks = p₁.indexMasks := u2.trans f2
  have v3 : q.pile = p₁.pile := u3.trans f3
  refine ⟨_, q, row, ?_, g2, ?_, v5.trans e2, e3⟩
  · rw [frontB_returns_at X P he hp h rs₀ gs₀]
    show ((claimCombinationBlock (Cl := Cl) X P).decide t₁ (rs.map noDigest) gs₁).bind _ = _
    rw [battB_of_part X P hp hb gs₁]
    exact k3
  · rw [← e1]
    show Sh.mk q.lin.isNone q.heard.isSome q.owed.isNone q.indexMasks (q.pile.map rowSh)
      q.d.st.codes (msgsOf q.d.st) = Sh.mk p₁.lin.isNone p₁.heard.isSome p₁.owed.isNone
        p₁.indexMasks (p₁.pile.map rowSh) p₁.d.st.codes (msgsOf p₁.d.st)
    rw [s2, u4, c1, v5, v1, v2, v3]

end AnyLens

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.frontB_is_part
#print axioms VerifiableInference.Desc.K13.Honest.battB_is_part
#print axioms VerifiableInference.Desc.K13.Honest.quietB_is_part
#print axioms VerifiableInference.Desc.K13.Honest.ready_of_partShape
#print axioms VerifiableInference.Desc.K13.Honest.m3Part_returns
#print axioms VerifiableInference.Desc.K13.Honest.frontB_returns_at
#print axioms VerifiableInference.Desc.K13.Honest.battB_of_part
#print axioms VerifiableInference.Desc.K13.Honest.quietB_of_part
#print axioms VerifiableInference.Desc.K13.Honest.battB_returns_at
#print axioms VerifiableInference.Desc.K13.Honest.quietB_returns_at
#print axioms VerifiableInference.Desc.K13.Honest.m3_returns_at
#print axioms VerifiableInference.Desc.K13.Honest.m3_returns_law

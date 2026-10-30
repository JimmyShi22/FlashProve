-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpSame.lean

Behind "publicOfO" (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) the plain set-up reads nothing that
hangs on the free numbers: where two public parts are alike in the sense of "SamePlans" and
"ProofFile.pubPlain" (Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean) returns at the files of the one, it returns
at the files of the other. One structure, three definitions, and theorems.

Main definitions:
* "SamePlans X X₀": ten fields: the same frame; the same layers' layout but for eps1, eps2, epsF;
  the same rd, wsLay, G, H, HLy; three numbers of the head's shape; as many plans of attention,
  and each pair with the same seam, ns, own and size of the forest.
* "turnP", "turnM", "turnZ": a record with its public part (in "turnZ": two files too) exchanged.

Main theorems:
* "links_same", "numbers_same", "rounds_same", "closing_same", "shapesWith_same", "shapesOf_same",
  "chains_same", "built_same": under "SamePlans" each of these functions gives the same at both.
* "planned_same", "sendsOf_same", "madeOf_same", "pubPlain_turn": the return is carried, with its
  value. Their proofs go after those of Johnson/LPFPol/PubPlain.lean.
* "pubPlain_same": there is a Z' that "ProofFile.pubPlain" returns at the other files, and Z'.p.X = X'.

Limits. Conditional on both returns of "publicOfO", on "SamePlans" and on the first return of
"ProofFile.pubPlain". At any hash o; the layout file is the same on both sides. The premise is
"SamePlans X' X", the new public part first: by its field "lay" the structure is not symmetric in
form.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.LPFPol.PubPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok atCall_ok atCall_of)
open VerifiableInference.PlanWritten (publicOfO)

structure SamePlans (X X₀ : Public) : Prop where
  frame : X.P.frame = X₀.P.frame
  lay : ∃ e1 e2 eF : Nat, X.layers.y =
    { X₀.layers.y with h := { X₀.layers.y.h with eps1 := e1, eps2 := e2, epsF := eF } }
  rd : X.layers.rd = X₀.layers.rd
  wsLay : X.layers.wsLay = X₀.layers.wsLay
  G : X.G = X₀.G
  H : X.H = X₀.H
  HLy : X.HLy = X₀.HLy
  head : X.hS.lt = X₀.hS.lt ∧ X.hS.lPd = X₀.hS.lPd ∧ X.hS.XL = X₀.hS.XL
  sizeA : X.A.size = X₀.A.size
  A : ∀ (g : Nat) (a a₀ : Attention.Plan), X.A[g]? = some a → X₀.A[g]? = some a₀ →
    a.seam = a₀.seam ∧ a.ns = a₀.ns ∧ a.own = a₀.own ∧ OnBytes.Model.forestSize a.fs = OnBytes.Model.forestSize a₀.fs

variable {X X₀ : Public}

theorem SamePlans.NGr (S : SamePlans X X₀) : X.NGr = X₀.NGr := by
  obtain ⟨e1, e2, eF, hy⟩ := S.lay
  show X.layers.y.NGr = X₀.layers.y.NGr
  rw [hy]

theorem SamePlans.p4 (S : SamePlans X X₀) : X.p4 = X₀.p4 := by
  obtain ⟨e1, e2, eF, hy⟩ := S.lay
  show X.layers.y.h.p4 = X₀.layers.y.h.p4
  rw [hy]
  rfl

/-- At each number both have a plan or neither has. -/
theorem SamePlans.atA (S : SamePlans X X₀) (g : Nat) :
    (X.A[g]? = none ∧ X₀.A[g]? = none) ∨ ∃ a a₀, X.A[g]? = some a ∧ X₀.A[g]? = some a₀ ∧
      a.seam = a₀.seam ∧ a.ns = a₀.ns ∧ a.own = a₀.own ∧
      OnBytes.Model.forestSize a.fs = OnBytes.Model.forestSize a₀.fs := by
  by_cases hg : g < X.A.size
  · have hg' : g < X₀.A.size := S.sizeA ▸ hg
    refine Or.inr ⟨X.A[g], X₀.A[g], Array.getElem?_eq_getElem hg, Array.getElem?_eq_getElem hg', ?_⟩
    exact S.A g _ _ (Array.getElem?_eq_getElem hg) (Array.getElem?_eq_getElem hg')
  · have hg' : ¬ g < X₀.A.size := S.sizeA ▸ hg
    exact Or.inl ⟨Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)⟩

/-- A function of what is the same gives the same array. -/
theorem SamePlans.mapA (S : SamePlans X X₀) {β : Type} (f : Attention.Plan → β)
    (hf : ∀ a a₀ : Attention.Plan, a.seam = a₀.seam → a.ns = a₀.ns → f a = f a₀) :
    X.A.map f = X₀.A.map f := by
  apply Array.ext
  · rw [Array.size_map, Array.size_map, S.sizeA]
  · intro i h1 h2
    rw [Array.size_map] at h1 h2
    rw [Array.getElem_map, Array.getElem_map]
    obtain ⟨q1, q2, -, -⟩ := S.A i _ _ (Array.getElem?_eq_getElem h1) (Array.getElem?_eq_getElem h2)
    exact hf _ _ q1 q2

theorem links_same (S : SamePlans X X₀) : ProofFile.Plain.linksPlain X = ProofFile.Plain.linksPlain X₀ := by
  unfold ProofFile.Plain.linksPlain
  rw [S.NGr, S.p4, S.G, S.H, S.mapA _ fun a a₀ q1 q2 => by rw [q1, q2]]

theorem numbers_same (S : SamePlans X X₀) (hp : Layer.HPlan2) (g : Nat) :
    layerNumbers X.layers hp g = layerNumbers X₀.layers hp g := by
  obtain ⟨e1, e2, eF, hy⟩ := S.lay
  unfold layerNumbers
  rw [S.rd, S.wsLay, hy]
  rfl

theorem rounds_same (S : SamePlans X X₀) : linkRounds X = linkRounds X₀ := by
  obtain ⟨e1, e2, eF, hy⟩ := S.lay
  have hfo : X.y.fo = X₀.y.fo := by
    show X.layers.y.fo = X₀.layers.y.fo
    rw [hy]
  have hH : ∀ moment, X.H.rounds X.hS X.HLy moment = X₀.H.rounds X₀.hS X₀.HLy moment := by
    intro moment
    unfold Head.HPlanH2.rounds Head.HPlanH2.own
    rw [S.H, S.HLy, S.head.1, S.head.2.1, S.head.2.2]
  funext link moment
  unfold linkRounds
  simp only [S.p4, S.NGr, S.G, hH, hfo, numbers_same S]
  rcases S.atA (link / if X₀.p4 = true then 2 else 1) with ⟨n1, n2⟩ | ⟨a, a₀, s1, s2, q1, -, q3, q4⟩
  · rw [n1, n2]
  · rw [s1, s2]
    simp only [Attention.rounds, q1, q3, q4]

theorem closing_same (S : SamePlans X X₀) : closingParts X = closingParts X₀ := by
  have e : closingPartsOf X = closingPartsOf X₀ := by
    funext g
    unfold closingPartsOf
    rw [S.G, S.p4]
    rcases S.atA g with ⟨n1, n2⟩ | ⟨a, a₀, s1, s2, q1, -, -, -⟩
    · rw [n1, n2]
    · rw [s1, s2]
      cases X₀.G[g]? with
      | none => rfl
      | some hp =>
        dsimp only
        rw [q1]
  unfold closingParts
  rw [S.NGr, e, S.H]

theorem shapesWith_same (S : SamePlans X X₀) (links : List Params.ReqLink) (layout : Params.ReqLayout)
    (ids : List Nat) : shapesWith X links layout ids = shapesWith X₀ links layout ids := by
  unfold shapesWith rangeChecksOf subproofsWith
  rw [closing_same S, S.wsLay, S.p4, S.NGr, rounds_same S]

theorem shapesOf_same (S : SamePlans X X₀) (lay : Option ByteArray) :
    ProofFile.Plain.shapesOf X lay = ProofFile.Plain.shapesOf X₀ lay := by
  unfold ProofFile.Plain.shapesOf
  simp only [links_same S, S.NGr, S.p4, S.frame, shapesWith_same S]

theorem chains_same {X X₀ : Public} (S : SamePlans X X₀) (lay : Option ByteArray) (cfg : ByteArray) :
    ProofFile.Plain.chainsOf X lay cfg = ProofFile.Plain.chainsOf X₀ lay cfg := by
  unfold ProofFile.Plain.chainsOf
  simp only [shapesOf_same S, S.frame]

theorem built_same {X X₀ : Public} (S : SamePlans X X₀) (ch : Chains) :
    ProofFile.Plain.builtOf X ch = ProofFile.Plain.builtOf X₀ ch := by
  unfold ProofFile.Plain.builtOf
  simp only [links_same S, S.NGr, S.p4, S.wsLay]

/-! ### the carriage, after Johnson/LPFPol/PubPlain.lean -/

def turnP (p : Planned) (X' : Public) : Planned := { p with X := X' }

def turnM (m : Johnson.G.OfPlan.Made) (X' : Public) : Johnson.G.OfPlan.Made := { m with p := turnP m.p X' }

def turnZ (Z : ProofFile.Pub) (pol' KL' : ByteArray) (X' : Public) : ProofFile.Pub :=
  { Z with pol := pol', KL := KL', made := turnM Z.made X' }

section
variable {o : Nat → ByteArray → ByteArray} {pol pol' KL KL' : ByteArray} {X X' : Public}

theorem planned_same {lay : Option ByteArray} (hX : publicOfO o pol KL lay = .ok X)
    (hX' : publicOfO o pol' KL' lay = .ok X') (S : SamePlans X' X) {p : Planned}
    (hp : ProofFile.Plain.planned o pol KL lay = .ok p) :
    ProofFile.Plain.planned o pol' KL' lay = .ok (turnP p X') := by
  unfold ProofFile.Plain.planned at hp ⊢
  obtain ⟨X0, h0, hp⟩ := exc_bind hp
  obtain rfl : X0 = X := Except.ok.inj (h0.symm.trans hX)
  obtain ⟨ch, hch, hp⟩ := exc_bind hp
  obtain ⟨b, hb, hp⟩ := exc_bind hp
  cases hp
  refine (bind_ok hX').trans ?_
  refine (bind_ok (a := ch) ((chains_same S _ _).trans hch)).trans ?_
  refine (bind_ok (a := b) ((built_same S _).trans hb)).trans ?_
  rfl

theorem sendsOf_same {lay : ByteArray} {p : Planned}
    (hp : ProofFile.Plain.planned o pol KL (some lay) = .ok p)
    (hp' : ProofFile.Plain.planned o pol' KL' (some lay) = .ok (turnP p X')) :
    ProofFile.PlainG.sendsOf o pol' lay KL' = ProofFile.PlainG.sendsOf o pol lay KL := by
  unfold ProofFile.PlainG.sendsOf
  rw [bind_ok hp, bind_ok hp']
  rfl

theorem madeOf_same {lay : ByteArray} (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL' (some lay) = .ok X') (S : SamePlans X' X) {m : Johnson.G.OfPlan.Made}
    (hm : ProofFile.PlainG.madeOf o pol lay KL = .ok m) :
    ProofFile.PlainG.madeOf o pol' lay KL' = .ok (turnM m X') := by
  unfold ProofFile.PlainG.madeOf at hm ⊢
  obtain ⟨p, hp, hm⟩ := exc_bind hm
  have hp' := planned_same hX hX' S hp
  obtain ⟨l, hl, hm⟩ := exc_bind hm
  refine (bind_ok hp').trans ?_
  refine (bind_ok (a := l) ((sendsOf_same hp hp').trans hl)).trans ?_
  split at hm
  · cases hm
    rfl
  · cases hm

theorem pubPlain_turn {lay : ByteArray} (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL' (some lay) = .ok X') (S : SamePlans X' X) {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ProofFile.pubPlain o pol' lay KL' = .ok (turnZ Z pol' KL' X') := by
  unfold ProofFile.pubPlain ProofFile.pubBy at hZ ⊢
  obtain ⟨m, hm, hZ⟩ := exc_bind hZ
  have hm' := atCall_of (n := "the plan") (madeOf_same hX hX' S (atCall_ok hm))
  refine (bind_ok hm').trans ?_
  dsimp only at hZ ⊢
  split at hZ
  · obtain ⟨_, e, _⟩ := exc_bind hZ
    cases e
  · rename_i hc
    obtain ⟨u, hu, hZ⟩ := exc_bind hZ
    obtain ⟨D, hD, hZ⟩ := exc_bind hZ
    obtain ⟨told, ht, hZ⟩ := exc_bind hZ
    obtain ⟨depth, hd, hZ⟩ := exc_bind hZ
    obtain ⟨cuts, hcu, hZ⟩ := exc_bind hZ
    obtain ⟨s0, hs, hZ⟩ := exc_bind hZ
    cases hZ
    rw [if_neg (show ¬ ((!(turnM m X').p.chains.proof.first.codes.lengthsOk) = true) from hc)]
    refine (bind_ok (a := u) hu).trans ?_
    refine (bind_ok (a := D) hD).trans ?_
    refine (bind_ok (a := told) ht).trans ?_
    refine (bind_ok (a := depth) hd).trans ?_
    refine (bind_ok (a := cuts) hcu).trans ?_
    refine (bind_ok (a := s0) hs).trans ?_
    rfl

end

theorem pubPlain_same {o : Nat → ByteArray → ByteArray} {pol pol' KL KL' lay : ByteArray} {X X' : Public}
    (hX : publicOfO o pol KL (some lay) = .ok X) (hX' : publicOfO o pol' KL' (some lay) = .ok X')
    (S : SamePlans X' X) {Z : ProofFile.Pub} (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ∃ Z', ProofFile.pubPlain o pol' lay KL' = .ok Z' ∧ Z'.p.X = X' :=
  ⟨_, pubPlain_turn hX hX' S hZ, rfl⟩

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.chains_same
#print axioms HonestTraceRun.SetUp.built_same
#print axioms HonestTraceRun.SetUp.pubPlain_same

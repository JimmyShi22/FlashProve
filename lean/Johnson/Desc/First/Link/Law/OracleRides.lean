-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OracleRides.lean: FOUR OF THE SEVEN RIDERS ON THE TABLE's MEANING
(`MgRides`, QuietRides.lean: «decodes», «held», «shown», «no collision») PAID AT A MEANING WHOSE
FOUR FIELDS ARE THE LIBRARY's OWN NOTIONS (Johnson/Desc/Sound/MeaningSig.lean: `decodesOf`,
`shownJT`, `noCollJT`; Johnson/Desc/SmpRows.lean: `smpHeld`), OVER A SUB-PROTOCOL THAT LEAVES THE
STATEMENT AND THE BOOK (our files call a sub-protocol a block). The composed meaning has these four
fields by definition. Theorems.

Why. The strings of the oracles behind a sub-protocol are what the library's stage leaves: the
committed table as it is, and every commitment tree that was sent in front of the sub-protocol
unturned (Johnson/Desc/Sound/StringsStay.lean). The three notions read the oracles through the
committed table, or through one tenant's tree, alone (Johnson/Desc/Sound/ReadsTreeAt.lean).

What is said.
  `out_strs`: the strings behind a piece's accepting transcript are what its stage leaves.
    `dec_rides`, `shown_rides`, `noColl_rides`, `held_rides`: the four riders. `OracleAsks`: what
    they take: every tenant whose pin is open sits in a tree below the piece's first tree (a test on
    the plan's numbers); the decoder of the committed table and the reader of the OOD samples answer
    alike at the two states of the verifier. `mgRides_of`: **`MgRides` from `OracleAsks`, `Rb`, and
    the three riders that are left** («in order», the public items, what they say beside their
    Bool).

Limits. THREE RIDERS ARE LEFT AS PREMISES. The two sentences on the decoder and on the samples'
reader are sentences on parameters of the composed meaning, which are letters there. `held_rides`
spends that the statement and the book are as they were: at the one equation's sub-protocol, which
adds an open row and takes mask entries, it does not serve as it stands. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.QuietRides
import Johnson.Desc.First.Link.Law.RbDef
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start openSets sampledIn)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}

/-- The strings behind a piece's accepting transcript are what its stage leaves. -/
theorem out_strs {T Cl W : Type} {p : Piece C F T Cl W} {a a' : T × F.E.Str}
    {τ : Iop.Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some a') :
    a'.2 = behind C F p.base p.ds a.2 τ := by
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

variable {P Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)

/-- «decodes» rides. -/
theorem dec_rides (z : P) (s s' : S) (base : ℕ) (ds : List RDT) (y : F.E.Str)
    (τ : Iop.Tr (uLT C ds)) (hd : ∀ c, decT c (z, s') = decT c (z, s))
    (h : decodesOf decT (z, s) (strsOf F y)) :
    decodesOf decT (z, s') (strsOf F (behind C F base ds y τ)) := by
  have h1 : decodesOf decT (z, s) (strsOf F (behind C F base ds y τ)) :=
    decodesOf_cell decT (z, s) (strsOf F y) (strsOf F (behind C F base ds y τ))
      (fun x => cellStays C F base ds y τ x) h
  unfold decodesOf at h1 ⊢
  rw [hd]
  exact h1

/-- «shown» rides, at a tenant of a tree that was sent in front. -/
theorem shown_rides (j t base : ℕ) (hj : j < base) (ds : List RDT) (y : F.E.Str)
    (τ : Iop.Tr (uLT C ds)) (h : shownJT cs G ms j t (strsOf F y)) :
    shownJT cs G ms j t (strsOf F (behind C F base ds y τ)) :=
  shownJT_col cs G ms j t (strsOf F y) (strsOf F (behind C F base ds y τ))
    (fun x => colStays C F base ds y τ j x hj) h

/-- «no collision» rides, at such a tenant. -/
theorem noColl_rides (z : P) (s s' : S) (j t base : ℕ) (hj : j < base) (ds : List RDT)
    (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (hs : smp (z, s') = smp (z, s))
    (h : noCollJT cs G smp ms j t (z, s) (strsOf F y)) :
    noCollJT cs G smp ms j t (z, s') (strsOf F (behind C F base ds y τ)) := by
  have h1 : noCollJT cs G smp ms j t (z, s) (strsOf F (behind C F base ds y τ)) :=
    noCollJT_col cs G smp ms j t (z, s) (strsOf F y) (strsOf F (behind C F base ds y τ))
      (fun x => colStays C F base ds y τ j x hj) h
  intro x hx hsit
  obtain ⟨w, hw, h2, h3⟩ := h1 x hx hsit
  exact ⟨w, by show smp (z, s') x.1 x.2 = some w; rw [hs]; exact hw, h2, h3⟩

/-- «held» rides where the statement and the book are as they were. -/
theorem held_rides (s s' : S) (R : Rb s s') (j t : ℕ) (h : smpHeld s.st s.book j t = true) :
    smpHeld s'.st s'.book j t = true := by
  rw [R.st, R.book]
  exact h

/-- **What the four riders take.** -/
structure OracleAsks (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k base : ℕ)
    (s s' : S) : Prop where
  /-- every tenant whose pin is open sits in a tree below the piece's first tree -/
  fence : ∀ x ∈ sampledIn Nm ((openSets links pl (start links))[k]?.getD []), x.1 < base
  /-- the decoder of the committed table answers alike at the two states -/
  dec : ∀ c, decT c (z, s') = decT c (z, s)
  /-- the reader of the OOD samples answers alike at the two states -/
  smp : smp (z, s') = smp (z, s)

/-- **MgRides FROM THE FOUR, AND THE THREE THAT ARE LEFT.** -/
theorem mgRides_of (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (pl : List Place) (z : P) (k : ℕ) (p : Place) (hD : Mg.decodes = decodesOf decT)
    (hS : Mg.shown = shownJT cs G ms) (hN : Mg.noColl = noCollJT cs G smp ms)
    (hH : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t) (base : ℕ)
    (ds : List RDT) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C ds))
    (hb : b.2 = behind C F base ds a.2 τ) (R : Rb a.1 b.1)
    (A : OracleAsks cs decT smp Nm links pl z k base a.1 b.1)
    (inOrder : Mg.inOrder (z, a.1) = true → Mg.inOrder (z, b.1) = true)
    (pub : First.pubHeld Mg ((openSets links pl (start links))[k]?.getD [])
        ((First.pubSets Mg.more links pl)[k]?.getD []) (z, a.1) = true →
      First.pubHeld Mg
        (First.stepOpen ((openSets links pl (start links))[k]?.getD []) (First.rowOf links p))
        (First.pubStep ((First.pubSets Mg.more links pl)[k]?.getD [])
          (First.pubRowM Mg.more links p)) (z, b.1) = true)
    (pubP : (∀ q ∈ (First.pubSets Mg.more links pl)[k]?.getD [], Mg.pubP q (z, a.1)) →
      ∀ q ∈ First.pubStep ((First.pubSets Mg.more links pl)[k]?.getD [])
        (First.pubRowM Mg.more links p), Mg.pubP q (z, b.1)) :
    MgRides Nm Mg links pl z k p a b where
  dec h := by
    rw [hD] at h ⊢
    rw [hb]
    exact dec_rides decT z a.1 b.1 base ds a.2 τ A.dec h
  inOrder := inOrder
  pub := pub
  pubP := pubP
  held x _ h := by
    rw [hH] at h ⊢
    exact held_rides a.1 b.1 R x.1 x.2 h
  shown x hx h := by
    rw [hS] at h ⊢
    rw [hb]
    exact shown_rides cs G ms x.1 x.2 base (A.fence x hx) ds a.2 τ h
  noColl x hx h := by
    rw [hN] at h ⊢
    rw [hb]
    exact noColl_rides cs G smp ms z a.1 b.1 x.1 x.2 base (A.fence x hx) ds a.2 τ A.smp h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.out_strs
#print axioms VerifiableInference.Desc.LinkJoin.dec_rides
#print axioms VerifiableInference.Desc.LinkJoin.noColl_rides
#print axioms VerifiableInference.Desc.LinkJoin.mgRides_of

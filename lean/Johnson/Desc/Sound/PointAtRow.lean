-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtRow.lean: "LIN point", THE ONE BLOCK OF THE SHARED CHAIN AT WHICH A SLOT's
OWN ENTERS, AT THE ROW's OWN TERMS (Johnson/Desc/Sound/SharedJointCountRowB.lean): what its files
owe, if its law is carried from the library's typed shared point. One statement written as `def … :
Prop`, and its proof: one call of the carriage in two parts (`leadsBN_carryS`,
Johnson/Desc/Plain/CarryBoth.lean) at the typed
point's two games (`LdLinP.pt_leadsB`, Johnson/Desc/Sound/PointGame.lean).

What is said. P: the library's typed test on the stored table. Under `FoldErr`: IF
  G: the block's one written round is read as the typed round of the shared point, by a reading that
    hangs on the key (the acting part at border 1) alone;
  hFK, hFO, hle: along G the errors δK bear the key's count εf · q^klo and δO a slot's own count
    (v + klo) · q^(v + klo - 1); and THE BLOCK's OWN ERRORS BEAR δK + N · δO;
  rd, hk: a statement at border 1 is read as a typed statement behind the sending of W, and its
    typed key (the encoded index and its record) is a function of the acting part;
  hon: the table's condition at border 1 gives the typed condition of j1 at the reading;
  hout: where the block says yes, the typed round puts out some b' at the transcript read by G; and
    "j2's condition at b', and every witness of j2 at b' gives one of j1 at the reading" gives the
    row's step at border 1 (`stepAt … 1`);
THEN the block has `LeadsBN` for N slots at its own errors, at the key, the condition and the step
OF THE ROW: the row's clause for block number 1. So of the point's law nothing of mathematics is
left to the block's files: a reading, two `Fits`, a tie of keys, and `hout` at its own text.

It is the plain twin of another statement, not in this library, `PointAtTable`
(Johnson/Desc/Sound/PointAtTable.lean), which ends in the form with witnesses' "pays".

Every "there is", walked. In `hout`: the typed transcript (determined by G) and the typed output
(determined by the typed round).
Limits. No reading, no P at the release's shape, no filling of the table's letters is shown.
`FoldErr` is a premise. A RULE: it would stay proved if the protocol were otherwise: it closes no
row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountRowB
import Johnson.Desc.Sound.PointGame
import Johnson.Desc.Plain.CarryBoth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open VerifiableInference.Desc.Shared

/-- **"LIN point" has the row's clause, by the carriage of the typed point's two games.** f: the
front block's piece; pt: the point's; r: the rest of the chain. -/
def PointAtRow : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
    [Fintype Y] (P : Cb.LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (εf N : ℕ) (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (Ns : NumbersS)
    (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt)
    (G : S₂ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)) →
      CarryS (uLT C pt.ds) P.pt.red.shape)
    (fk : S₂ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)) →
      (ι → P.Sy) × P.D.X.Rec)
    (δK δO : Err (uLT C pt.ds)) (rd : (P₁ × S₂) × Fr.E.Str → P.X1 × P.E1.Str),
    P.FoldErr on0 εf →
    Err.le (Err.add δK (Err.times N δO)) pt.err →
    (∀ k, (G k).Fits ((εf * Fintype.card E ^ P.D.klo, ()) : ℕ × Unit) δK) →
    (∀ k, (G k).Fits
      (((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1), ()) : ℕ × Unit) δO) →
    (∀ a, P.k1 (rd a) = fk (keyAt Prod.snd Ns.lo f (pt :: r) 1 a)) →
    (∀ a, onQ₂ Ns Pm Oc split f (pt :: r) 1 a → (P.j1 on0).on (rd a)) →
    (∀ a τ b, onQ₂ Ns Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ∃ τ' b', (G (keyAt Prod.snd Ns.lo f (pt :: r) 1 a)).tr τ = some τ' ∧
        P.pt.red.out (rd a) τ' = some b' ∧
        (((P.j2 on0).on b' ∧ ∀ w', (P.j2 on0).relR b' w' → (P.j1 on0).relR (rd a) w'.2) →
          stepAt Ns Mg Pm Oc split f (pt :: r) ext 1 a b)) →
    pt.ior.red.LeadsBN (keyAt Prod.snd Ns.lo f (pt :: r) 1) (onQ₂ Ns Pm Oc split f (pt :: r) 1)
      (stepAt Ns Mg Pm Oc split f (pt :: r) ext 1) N pt.err

theorem pointAtRow : PointAtRow := by
  intro E ι κ J Y _ _ _ _ _ _ _ P on0 εf N P₁ S₂ Cl Wt C Fr Ns Mg Pm Oc split f pt r ext G fk δK δO
    rd hF hle hFK hFO hk hon hout
  exact leadsBN_carryS pt.ior.red P.pt.red _ P.k1 G fk _ _ δK δO N pt.err hle hFK hFO rd hk _
    (P.j1 on0).on _ _ hon hout (P.pt_leadsB on0 εf hF)

#check @PointAtRow

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pointAtRow

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4ReadsOf.lean: THE STRUCTURE K4Reads (Johnson/Road/K4/K4Reads.lean: what the
data's letters read of the verifier's state, from a state in a layers' segment to the state where
the sub-protocol K4 has accepted) OUT OF EQUATIONS ON THESE LETTERS, GENERAL IN THE DATA D: no
composed meaning's own data is named.

  `rw_at`: the line rw where the reader of the rows on the committed table is the reader through
    the state's own book, rwBook arr mat (Johnson/Desc/K13/Law/ReaderByBook.lean): by rwBook_rest
    (Johnson/Road/K4/RwBookRest.lean).
  `req_pub`: the line req where the field req of the letter H reads the public part alone: req_at
    (Johnson/Road/K4/K4ReadsAt.lean) at a function that leaves the state's field aside.
  **`k4Reads_at`**: all seven lines. PREMISES, none paid here, each owed by whoever fills D:
    hrw, hreq, hsmp, hSt: four equations "the letter is that term" · hN: Stored.NoRec D.decT
    (Johnson/Desc/First/Look/K3StoredThree.lean: the decoder of the committed table does not read
    the verifier's state) · hbase, hhead: the lines base and head as they stand in K4Reads.
The line decT is NoRec unfolded. Another file has the same line as a lemma at Rest
(table_of_noRec, Johnson/Road/K4/K4PinsConduit.lean):
not imported.
Limits. It is a structure of sentences on what letters read: nothing is said of any sub-protocol or
witness. That the composed meaning's letters are these terms is shown here at no filling. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4ReadsAt
import Johnson.Road.K4.RwBookRest
import Johnson.Desc.First.Look.K3StoredThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (Stored.NoRec)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.K13.Law (rwBook)
open VerifiableInference.Desc.Sound (Frame strsOf GQ Stated smpNamed)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {D : K4Data Xi P Tok rows cols nR kC X} (Z : P)

/-- **The line rw**, where the letter is the reader through the state's own book. -/
theorem rw_at {arr : ℕ → ℕ → ℕ}
    {mat : CellsK rows cols → Fin nR → (Fin kC → Bool) → OnBytes.Slice.GE}
    (hD : D.rw13 = rwBook arr mat) :
    ∀ s s', LayRest s s' → D.rw13 (Z, s') = D.rw13 (Z, s) := by
  intro s s' h
  rw [hD]
  exact rwBook_rest arr mat Z h.2

/-- **The line req**, where the letter's field req reads the public part alone. -/
theorem req_pub {R : P → P5J.TReq} (hD : D.H.req = fun a => R a.1) :
    ∀ s s', LayRest s s' → D.H.req (Z, s) = D.H.req (Z, s') :=
  req_at Z (f := fun z _ => R z) hD

/-- **K4Reads out of four equations on the data's letters, NoRec, and the lines base and head.** -/
theorem k4Reads_at (Fr : Frame) (base : ℕ) {arr : ℕ → ℕ → ℕ}
    {mat : CellsK rows cols → Fin nR → (Fin kC → Bool) → OnBytes.Slice.GE}
    {R : P → P5J.TReq} {seats : List (ℕ × ℕ)} {u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ}
    (hrw : D.rw13 = rwBook arr mat) (hN : Stored.NoRec D.decT)
    (hreq : D.H.req = fun a => R a.1) (hsmp : D.smp = smpNamed D.cs seats)
    (hSt : D.St = Stated.of u)
    (hbase : ∀ s s', LayRest s s' → D.base (Z, s) = true → D.base (Z, s') = true)
    (hhead : ∀ s s' (x y : Fr.E.Str), LayRest s s' → SameStr Fr base x y → ∀ p i w,
      D.headPart p i (Z, s') (strsOf Fr y) w → D.headPart p i (Z, s) (strsOf Fr x) w) :
    K4Reads D Z Fr base where
  rw := rw_at Z hrw
  decT := fun s s' _ c => hN c Z s' s
  req := req_pub Z hreq
  head := hhead
  smp := smp_at Z hsmp
  base := hbase
  stMask := stMask_at hSt

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.rw_at
#print axioms OnBytes.Road.K4.req_pub
#print axioms OnBytes.Road.K4.k4Reads_at

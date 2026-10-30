-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkJoinA.lean: THE JOIN AT THE FULL SIZE, FIRST PART: what the chain's yes
(run_viewOf_full, Johnson/Prover/Link/ChainAtFull.lean) asks of the view at linkNext beside the walk
over the blocks. Statements and proofs; each is a call of laws that are proved in other files.
The join: the proof of link_yes (LinkJoinF.lean), in six files: LinkJoinA to LinkJoinF.

  rs_full       the view of LinkFrame.lean (viewOf) at linkNext has linkAll's rounds, at every run
  fit_full      these rounds pass roundsFit at the chain's declared rounds
  okView_full   the view's words are below the prime
  served_full   every declared column is there, with its width

Not shown here. The walk. Nothing on soundness; nothing on what any value that is sent discloses or
does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkYesStm
import Johnson.Prover.Link.LinkWords
import Johnson.Prover.Link.LinkView
import Johnson.Prover.Link.ChainAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open _root_.Desc.K15 (frP linkDeclaredRounds)
open OnBytes.Flat (dsFull RecFull)
open _root_.Run.PQ (SgX)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)

variable (t : ℕ) (X : LIn frS) (C : LCoins) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
  (ρ : Rho (uL (ckP .two) dsFull))

theorem rs_full : rvOf dsFull 0 [] (linkNext frP frS t X C) (drawnSL (ckP .two) dsFull ρ) =
    (linkAll frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ))).rs :=
  rvOf_link frP frS t X C dsFull _ (length_drawnSL _ _ ρ)
    (by rw [linkAll_length frP frS t X C _ frFirst frRest fr_cons, fr_rounds])
    (by rw [linkAll_items frP frS t X C _ frFirst frRest fr_cons, fr_sorts])

theorem fit_full : roundsFit (linkDeclaredRounds frP)
    (rvOf dsFull 0 [] (linkNext frP frS t X C) (drawnSL (ckP .two) dsFull ρ)) = true :=
  roundsFit_rvOf _ (linkDeclaredRounds frP) dsFull fr_isOf2 fr_nz 0 [] ρ

theorem okView_full
    (hy : ∀ p, (((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y p).2.all (· < fieldPrimeWord)) = true) :
    viewWordsBelowPrime (viewOf dsFull frS.P.T.a frD.xs (linkNext frP frS t X C) y
                  (drawnSL (ckP .two) dsFull ρ)) = true :=
  okViewW_run (linkNext frP frS t X C) dsFull frS.P.T.a frD.xs y (linkNext_vals frP frS t X C)
    (linkNext_cols frP frS t X C) hy ρ

theorem served_full
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
      ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2048) :
    Served (lookV dsFull frS.P.T.a (linkNext frP frS t X C) y (drawnSL (ckP .two) dsFull ρ))
      ((groupsOf 0 (linkDeclaredRounds frP) (drawnSL (ckP .two) dsFull ρ)).flatMap id) :=
  served_viewOf dsFull frS.P.T.a frD.xs (linkDeclaredRounds frP) _ y _ (fun _ => 2048) fr_wantTie fr_wideTie
    fr_opens (length_drawnSL _ _ ρ) (fun j k d s hd hs h x => linkNext_wide t X C j k d s hd hs h x)
    hy

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.rs_full
#print axioms Johnson.Prover.Link.fit_full
#print axioms Johnson.Prover.Link.okView_full
#print axioms Johnson.Prover.Link.served_full

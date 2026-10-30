-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/NoneNearCand.lean: a sampled member without a candidate refutes the relation in
front of the proximity test's chain; and the batching's converse at the Johnson bound's list.
Statements and proofs.

The relation in front is `NoneNear` (Johnson/Desc/K12/Law/BatJoint.lean). No frame, no view and no
program stands in this file, and there is no new mathematics.
Main names:
  `noneNear_of_noCand`: l: sampled messages' shapes with their radii, each with a seat in the stage
    s, no two rows at one place; f: their words as sent; σ: their samples; e fits each member's
    radius in leaves. Let the member i have no candidate (the library's `OMsg.Cand`: a message in
    its word's list that has the sample's answers), and let r be one of the batched rows such that,
    of every near witness's own words, "r holds" gives "the member's share has the sample's
    answers". (This premise, hS, is asked of the witnesses within e of the group's word alone. Of a
    far witness it may be false: the rows beyond a member's real ones inside its block may hold
    anything there, and the row's value counts them. For the member's sample row as a record holds
    it, `says_sample_ge` of Johnson/Desc/K12/Law/FormTake.lean is that equivalence in the rows'
    terms; `says_sample` of Johnson/Desc/K12/Law/SaysSample.lean speaks of the own row of
    `Send.form`, whose target is 0.) Then `NoneNear`: no witness within e positions of the group's
    word holds words of which all the rows hold. By the library's `Site.share` (`gp_share`,
    Johnson/Desc/K12/Law/ShareNear.lean): every near witness's share at i is in i's list.
  `batCatches_joh`: at a stage and radius with the library's `Sg.StageJ` (the yes of `johOk` gives
    it: `stageJ_of_L`, Johnson/Desc/K12/Law/ChainJoh.lean): the batching's converse
    (`batCatches_bare`, Johnson/Desc/Means/BatCatchesProof.lean) at lst := Sg.lstJ s e, the Johnson
    bound's list; `ListAt` by the library's `Sg.listJ_of`.
  `few_draws_of_noCand`: the two joined: a member without a candidate gives that the values of the
    drawn element at which the batched claim has a witness are at most Sg.lstJ s e · (rows.size −
    1).
Read with `TestGivesCand` (Johnson/Desc/Sound/WordsLaw.lean): where some member has no candidate,
but for these few draws the claim at which the chain starts has no witness: the premise of
`chain_many` (OnBytes/Slice/ManySem.lean).
Limits:
(1) hS is a premise here. Johnson/Desc/K12/Law/FormTake.lean pays it at the row that the record
holds (`answers_of_says_g`; `answers_of_says` of Johnson/Desc/K12/Law/ShareWords.lean spoke of the
own row of `Send.form`, whose target is 0) from `says_sample_ge`, `words_share` (the words at the
member's entries are the share) and `Padded` for near witnesses (`blank_of_near`, `padded_wordsOf`
under `RowsBlank`). That the member's sample row stands among the batched rows with the record's
seed and answer is not shown.
(2) The group is `gpOfList` (each member's format from its own shape), not the law's `gpG` (limit
(1) of Johnson/Desc/K12/Law/ShareNear.lean).
(3) Members without a sample have no candidate to lack: nothing is said on them.
(4) It is a count of values θ of the drawn element: the game's form and the reading of the draw are
not here.
(5) l, seat, f, σ and r are free letters.
(6) As in the files on the batching's converse under Johnson/Desc/Means, which lie beneath: nothing
on who draws the batching's element, or when, or on how its readings are spread over the field.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `sig_inList_iff`
(Cb/Ld/LdSigProofs.lean), `Sg.listJ_of` (OnBytes/Slice/BlocksJohnson.lean), `Sg.fit_cIn`
(OnBytes/Slice/Numbers.lean); `batCatches_bare`; `gp_share`.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.ShareNear
import Johnson.Desc.K12.Law.ChainJoh
import Johnson.Desc.Means.BatCatchesProof

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice Johnson.Pack
open OnBytes.Means H2K.ClaimSays

/-- A sampled member without a candidate refutes the relation in front. -/
theorem noneNear_of_noCand (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) {s : Sg}
    (seat : ∀ i : Fin l.length, Site s (mbOfShape cs (l.get i).1 (l.get i).2))
    (hA : (gpOfList cs l seat).Apart) (f : (sigOf cs l).ext.Str) (σ : (sigOf cs l).Smp) (e : ℕ)
    (hfit : ∀ i : Fin l.length, e < ((l.get i).2 + 1) * 2 ^ (s.C.a - aOf cs (l.get i).1))
    (S' : Statement) (L : GroupLayout) (rows : Array Row) (i : Fin l.length) (r : Row)
    (hr : r ∈ rows.toList)
    (hS : ∀ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext)
        ((gpOfList cs l seat).word fun i => ((sigOf cs l).om i).upW (f i))
        (s.cIn.N.enc w.1 w.2) ≤ e → Says rdE S' r (wordsOf S' L (tabOf s w.1)) →
      ((sigOf cs l).om i).Z.val (σ i).1 (fun j => w.1 ((seat i).atJ j)) = (σ i).2)
    (hno : ∀ m, ¬ ((sigOf cs l).om i).Cand (f i) (σ i) m) :
    NoneNear s e S' L rows
      ((gpOfList cs l seat).word fun i => ((sigOf cs l).om i).upW (f i)) := by
  intro w hn hall
  obtain ⟨r', hr'⟩ := gp_share (gpOfList cs l seat) hA _ e w hn hfit i
  exact hno _ ⟨(sig_inList_iff GE ((sigOf cs l).om i) (f i) _).1 ⟨(_, r'), hr', rfl⟩, hS w hn (hall
      r hr)⟩

/-- The batching's converse at the Johnson bound's list. -/
theorem batCatches_joh (s : Sg) (e : ℕ) (hJ : s.StageJ e) (S' : Statement) (g : Nat) (L :
    GroupLayout)
    (rows : Array Row) (y : s.cIn.Word) (ht : combineAt S' g ⟨L, rows⟩ = true)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l)
    (hz : 2 ^ L.logEllZk = s.Z.l) : BatCatches s e (s.lstJ e) S' g L rows y :=
  batCatches_bare s e (s.lstJ e) S' g L rows y (Sg.listJ_of (Sg.fit_cIn hJ.sized) hJ.joh) ht hk hh
      hl hz

/-- A member without a candidate: few draws at which the batched claim has a witness. -/
theorem few_draws_of_noCand (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) {s : Sg}
    (seat : ∀ i : Fin l.length, Site s (mbOfShape cs (l.get i).1 (l.get i).2))
    (hA : (gpOfList cs l seat).Apart) (f : (sigOf cs l).ext.Str) (σ : (sigOf cs l).Smp) (e : ℕ)
    (hJ : s.StageJ e)
    (hfit : ∀ i : Fin l.length, e < ((l.get i).2 + 1) * 2 ^ (s.C.a - aOf cs (l.get i).1))
    (S' : Statement) (g : Nat) (L : GroupLayout) (rows : Array Row)
    (ht : combineAt S' g ⟨L, rows⟩ = true) (hk : L.k = s.h + s.g) (hh : L.h = s.h)
    (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk = s.Z.l) (i : Fin l.length) (r : Row)
    (hr : r ∈ rows.toList)
    (hS : ∀ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext)
        ((gpOfList cs l seat).word fun i => ((sigOf cs l).om i).upW (f i))
        (s.cIn.N.enc w.1 w.2) ≤ e → Says rdE S' r (wordsOf S' L (tabOf s w.1)) →
      ((sigOf cs l).om i).Z.val (σ i).1 (fun j => w.1 ((seat i).atJ j)) = (σ i).2)
    (hno : ∀ m, ¬ ((sigOf cs l).om i).Cand (f i) (σ i) m) :
    cnt (BadDraws s e S' g L rows
      ((gpOfList cs l seat).word fun i => ((sigOf cs l).om i).upW (f i))) ≤
      s.lstJ e * (rows.size - 1) :=
  batCatches_joh s e hJ S' g L rows _ ht hk hh hl hz
    (noneNear_of_noCand cs l seat hA f σ e hfit S' L rows i r hr hS hno)

end H2K.Pin

#print axioms H2K.Pin.noneNear_of_noCand
#print axioms H2K.Pin.batCatches_joh
#print axioms H2K.Pin.few_draws_of_noCand

-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TokensAtState.lean: THE TOKENS THAT THE FIRST CHAIN's RECORD HOLDS ARE THE LIBRARY's
FUNCTION OF THE REQUEST's TOKENS, WHERE THE RECORD's WORDS ARE THE REQUEST FILE's. A layers' link
reads the tokens off the record (`S.tokv`, Johnson/Desc/First/State.lean: a function of the words
`S.req`). The model's relation reads `Cm.Seg.tokX x` (Cm/ReqModel.lean) at a request x of the frame,
which a description whose instance holds the request file's bytes reads back by `backReq`
(Johnson/Meaning/ReqBytes.lean). Here the two are one function on all numbers. WITHOUT A KIND.
Book-keeping on arrays; definitions unfolded.

  `prompt_of_backReq`: what `backReq` returns has the file's words as its tokens, and the file has
    T + 2 words: `unlayB`'s own text (Johnson/Flat/LayBytes.lean).
  `tokv_tie`: s.req = words32 b, backReq b = some r: (fun p => s.tokv.getD p 0) =
    tokX (putReq r t).val, at every t: both are 0 from place T on.

KIN: `Meaning.Emb.tokens_tie` (Johnson/Goal/Meaning/EmbTokens.lean [not in this library]) is that
sentence for the array that the request's reader in `verify-on-bytes` makes (`coveredOf`); its head:
"Not claimed: that the description's state holds this array". Its three tools are called here
(`getD_map_lt`, `getD_ge`, Johnson/Road/FormsKeysEq.lean; `Hd.getD_cut`,
Johnson/Road/HeadWeight.lean). That `putReq` (Johnson/Flat/TiesAtReq.lean) leaves the tokens: the
`Meaning.tokX_putReq` (Johnson/Goal/Meaning/RowLocal.lean), called.

Limits. That a record's words ARE the request file's is a premise (hs): at the table of joints it is
a conjunct of "in order" that other files lay. That a description reads its request by `backReq`,
and puts a token in by `putReq`, is its filler's. The reference sizes alone. Nothing on soundness.

-/
import Johnson.Desc.First.State
import Johnson.Meaning.ReqBytes
import Johnson.Goal.Meaning.RowLocal
import Johnson.Road.FormsKeysEq
import Johnson.Road.HeadWeight
import Cm.ReqModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Flat OnBytes.Road OnBytes.Model.Verify
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (Req WellFormed)
open VerifiableInference.Desc.First (S)

/-- **What `backReq` returns has the file's words as its tokens**, and the file has T + 2 words. -/
theorem prompt_of_backReq {b : ByteArray} {r : Req} (h : Meaning.backReq b = some r) :
    (words32 b).size = ppref.T + 2 ∧
      ∀ t : Fin ppref.T, (r.val.prompt t).val = ((words32 b).getD t.val 0).toNat := by
  unfold Meaning.backReq at h
  cases hu : unlayB (P := ppref) (b, ⟨0, ppref_V_pos⟩) with
  | none =>
    rw [hu] at h
    cases h
  | some i =>
    rw [hu, Option.bind_some] at h
    split at h
    · have e : r.val = i := by rw [← Option.some.inj h]
      unfold unlayB at hu
      split at hu
      · rename_i hf
        have e2 := Option.some.inj hu
        rw [e, ← e2]
        exact ⟨hf.2.1, fun _ => rfl⟩
      · cases hu
    · cases h

/-- **THE TOKENS' TIE AT THE RECORD**: where the record's words are the request file's and `backReq`
reads r off that file: the record's tokens, read with the default 0, are the library's function of
the tokens of r with any token put in. -/
theorem tokv_tie {b : ByteArray} {r : Req} (h : Meaning.backReq b = some r) {s : S}
    (hs : s.req = words32 b) (t : Fin ppref.V) :
    (fun p => s.tokv.getD p 0) = Cm.Seg.tokX (putReq r t).val := by
  obtain ⟨hsz, hp⟩ := prompt_of_backReq h
  have hT : s.reqT = ppref.T := by
    unfold S.reqT
    rw [hs, hsz]
    rfl
  have hx : (s.req.extract 0 ppref.T).size = ppref.T := by
    rw [Array.size_extract, hs, hsz]
    omega
  rw [Meaning.tokX_putReq]
  funext p
  show s.tokv.getD p 0 = Inst.Model.All.tokOf r.val.prompt p
  unfold Inst.Model.All.tokOf S.tokv
  rw [hT]
  by_cases hlt : p < ppref.T
  · rw [dif_pos hlt, hp ⟨p, hlt⟩, getD_map_lt _ _ (by rw [hx]; exact hlt) 0 0,
      Hd.getD_cut _ (by rw [hs, hsz]; omega) hlt, hs]
  · rw [dif_neg hlt]
    exact getD_ge _ (by rw [Array.size_map, hx]; omega) 0

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.prompt_of_backReq
#print axioms OnBytes.Road.K4.tokv_tie

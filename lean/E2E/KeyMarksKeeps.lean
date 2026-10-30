--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMarksKeeps.lean: EVERY SUB-PROTOCOL OF THE KEY FILE's FIRST CHAIN IN FRONT OF "rng.0.rows"
KEEPS THE MARK "NO WRITTEN-OUT FACTOR", FROM ITS OWN ACCEPT ALONE: where it accepts from s to s'
and `PlainAll s` holds (E2E/KeyMarksWalk.lean: no row of the statement, and no row that the lookups
have written, has a written-out factor), `PlainAll s'` holds. At all values; no hypothesis on what
was heard, on rooms or on public numbers. Steps of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

Why. `link_plain` and `links_plain` of KeyMarksWalk.lean stand under the hypotheses by name of
E2E/KeyRowsFit.lean and E2E/KeyFirstHalf.lean, under which a link's fold is written out. A rule
that carries the mark along a run, border by border, wants of each sub-protocol a law from its own
accept.

  `idx_keeps`, `msg_keeps`   the two sendings.
  `caller_keeps`, `k3_keeps`, `claims_keeps`, `layer_keeps`   in a lookup's link: the caller (it
      takes mask entries twice); the lookup's own sub-protocol in its seat (it turns the lookups'
      ledger and what was heard); the three runs of claims, which the layer calls (they turn the
      ledger); the layer (it writes the rows that `rowsInOrder` returns: `rows_noDense`,
      E2E/KeyRowsNoDense.lean).
  ★ `link_member_keeps`   each of the six sub-protocols of a link's flat list: "laid", the caller,
      the lookup's own, the layer, "behind the batching", "cleared"; the first and the fifth return
      the state as it was, the last clears the ledger, what was heard and the homes.
  ★★ `front_member_keeps`   each sub-protocol of the list: the two sendings, then all lookups'
      links.

Behind "rng.0.rows" the two marks of the ranges' test come from that sub-protocol's accept and
`PlainAll` in front: `layRows_plain` (KeyMarksWalk.lean), as it stands.

By what. Of the library: `callerD_law`, `layerD_law` (Johnson/RunOne/Law/AtKeyD.lean); `link_flat`
(Johnson/RunOne/Law/LinkSeats.lean); `lay_ok`, `after_ok`, `clear_ok` (Johnson/RunOne/KeyTen.lean);
`block_law`, `runIn_ok` (Johnson/Desc/First/Look/KeyLaw/). `claims_keeps` follows the proof of the
library's `claims_d` (Johnson/RunOne/Law/StepSide4.lean), which says of the same runs that they
leave the field d; here the written rows besides. Ours: `idx_plain`, `msg_plain`,
`takeMasks_plain`, `rows_noDense`.

Limits. FORM ALONE: that a row holds of anything is not touched. That `PlainAll` holds at a chain's
first state is asked of whoever calls. No rule along a run is typed here. Nothing on completeness,
on soundness or on what a view shows.


-/
import E2E.KeyMarksWalk
import Johnson.RunOne.Law.AtKeyD
import Johnson.RunOne.Law.LinkSeats
import Johnson.RunOne.KeyTen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.K3.KeyLaw (bindB runIn_ok bindX namedX block_law)
open VerifiableInference.Desc.Ground.Sh (stPlainB rowPlainB takeMasks_plain)
open Johnson.RunOne.Law.AtKeyD (callerD_law layerD_law)
open Johnson.RunOne.Law.LinkSeats (link_flat)
open Johnson.RunOne.KeyRows1 (lay_ok after_ok clear_ok)

/-- "idx.1.send". -/
theorem idx_keeps {one : Params.OneTime} {N : Pieces} {groups : List (List ℕ)}
    {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendIndexMasks (Cl := Key.Claim) one N groups).decide s rs gs = .ok s')
    (hA : PlainAll s) : PlainAll s' := by
  obtain ⟨p, b⟩ := idx_plain e hA.1
  exact ⟨p, by rw [b]; exact hA.2⟩

/-- "msg.1.send". -/
theorem msg_keeps {one : Params.OneTime} {N : Pieces} {groups : List (List ℕ)}
    {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendOwnMessage (Cl := Key.Claim) one N groups).decide s rs gs = .ok s')
    (hA : PlainAll s) : PlainAll s' := by
  obtain ⟨p, b⟩ := msg_plain e hA.1
  exact ⟨p, by rw [b]; exact hA.2⟩

/-- The caller. -/
theorem caller_keeps {one : Params.OneTime} {i : ℕ} {x : Lookup} {s s' : FirstState}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (caller one i x).decide s rs gs = .ok s') (hA : PlainAll s) : PlainAll s' := by
  obtain ⟨-, -, o, k, e1, e2, -, rfl⟩ := callerD_law h
  exact ⟨takeMasks_plain _ k.2 _ _ k.1 e2 (takeMasks_plain _ o.2 _ _ o.1 e1 hA.1), hA.2⟩

/-- The lookup's own sub-protocol in its seat. -/
theorem k3_keeps {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG} {s s' : FirstState}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (lookupKind lookupSeat before bits [] p : Block FirstState Key.Claim).decide s rs gs = .ok s')
    (hA : PlainAll s) : PlainAll s' := by
  obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ _ _ _ _ h
  exact ⟨hA.1, hA.2⟩

/-- The link's three runs of claims leave the field d and the written rows. -/
theorem claims_keeps {b0 : Block FirstState Key.Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG}
    {s s' : FirstState} {cls : List Key.Claim}
    (h : claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")] s = .ok (cls, s')) :
    s'.d = s.d ∧ s'.base.rows = s.base.rows := by
  unfold claimsIn claimsInBy at h
  simp only [List.foldl_cons, List.foldl_nil] at h
  obtain ⟨x2, h, h3⟩ := bindB h
  obtain ⟨x1, h, h2⟩ := bindB h
  obtain ⟨x0, h0, h1⟩ := bindB h
  cases h0
  obtain ⟨z1, r1, rfl⟩ := runIn_ok (o := (1, "objects")) rfl h1
  obtain ⟨z2, r2, rfl⟩ := runIn_ok (o := (1, "planes")) rfl h2
  obtain ⟨z3, r3, e3⟩ := runIn_ok (o := (1, "guests")) rfl h3
  obtain ⟨F1, a1, r1⟩ := bindX r1
  obtain ⟨g1, a2, r1⟩ := bindX r1
  cases r1
  obtain ⟨F2, b1, r2⟩ := bindX r2
  obtain ⟨g2, b2, r2⟩ := bindX r2
  obtain ⟨_, -, r2⟩ := bindX r2
  obtain ⟨y, b4, r2⟩ := bindX r2
  obtain ⟨l, b5, r2⟩ := bindX r2
  cases r2
  have h9 := namedX r3
  cases h9
  obtain ⟨-, rfl⟩ := Prod.mk.inj e3
  exact ⟨rfl, rfl⟩

/-- The layer. -/
theorem layer_keeps {one : Params.OneTime} {set : Params.Setting} {i : ℕ} {x : Lookup}
    {b0 : Block FirstState Key.Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG}
    {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (layer one set i x (claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")])).decide s rs gs = .ok s')
    (hA : PlainAll s) : PlainAll s' := by
  obtain ⟨cls, s1, F, g', rows, keys, e1, -, -, hrows, -, rfl⟩ := layerD_law h
  obtain ⟨ed, er⟩ := claims_keeps e1
  refine ⟨?_, fun r hr => ?_⟩
  · show stPlainB s1.d.st = true
    rw [ed]
    exact hA.1
  · have hr' : r ∈ (s1.base.rows ++ [rows]).flatten := hr
    rw [List.flatten_append, List.mem_append] at hr'
    rcases hr' with c | c
    · rw [er] at c
      exact hA.2 r c
    · exact rows_noDense hrows r (by simpa using c)

/-- ★ **EACH OF THE SIX SUB-PROTOCOLS OF A LINK's FLAT LIST.** -/
theorem link_member_keeps (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup)
    {c : Block FirstState Key.Claim} (hc : c ∈ (lookupLink one set i x).blocksInOrder) {s s' : FirstState}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (h : c.decide s rs gs = .ok s')
    (hA : PlainAll s) : PlainAll s' := by
  obtain ⟨c0, c4, c5, hf, h0, h4, h5⟩ := link_flat one set i x
  rw [hf] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h0] at h
    obtain rfl := lay_ok one set i x s s' h
    exact hA
  · exact caller_keeps h hA
  · exact k3_keeps h hA
  · exact layer_keeps h hA
  · rw [h4] at h
    obtain rfl := after_ok one set i x s s' h
    exact hA
  · rw [h5] at h
    obtain rfl := clear_ok one set i x s s' h
    exact ⟨hA.1, hA.2⟩

/-- ★★ **EACH SUB-PROTOCOL IN FRONT OF "rng.0.rows".** -/
theorem front_member_keeps (one : Params.OneTime) (set : Params.Setting) (N : Pieces)
    (g₁ g₂ : List (List ℕ)) {c : Block FirstState Key.Claim}
    (hc : c ∈ [sendIndexMasks (Cl := Key.Claim) one N g₁, sendOwnMessage one N g₂] ++
      ((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1).flatMap Link.blocksInOrder)
    {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : c.decide s rs gs = .ok s') (hA : PlainAll s) : PlainAll s' := by
  rcases List.mem_append.1 hc with hc | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact idx_keeps h hA
    · exact msg_keeps h hA
  · obtain ⟨L, hL, hcL⟩ := List.mem_flatMap.1 hc
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hL
    exact link_member_keeps one set x.2 x.1 hcL h hA

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.idx_keeps
#print axioms AtPublicFiles.KeyLookup.msg_keeps
#print axioms AtPublicFiles.KeyLookup.caller_keeps
#print axioms AtPublicFiles.KeyLookup.k3_keeps
#print axioms AtPublicFiles.KeyLookup.claims_keeps
#print axioms AtPublicFiles.KeyLookup.layer_keeps
#print axioms AtPublicFiles.KeyLookup.link_member_keeps
#print axioms AtPublicFiles.KeyLookup.front_member_keeps

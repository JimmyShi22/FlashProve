-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkFrameServed.lean: BESIDE THE COPY's FILE's FRAME
(Johnson/Prover/Link/LinkFrame.lean, LinkFrameView.lean): EVERY COLUMN THAT THE DRAWS ASK FOR IS
THERE, WITH ITS WIDTH: looked up by key and position as a one-chain file's laws look a column up
(lookY, Johnson/Desc/Plain/OneChain.lean): in the two stored strings, or among the strategy's own
columns (colOf).

Main names (namespace Johnson.Prover.Link).
  wantedXL_key   a wanted pair stands under a stored string's key or under an own tree's number.
  look_wanted   THE STATEMENT: "some c"; c has that stored string's width under a stored key (each
      of the two strings has a width of its own), the tree's width under an own number.

By calls: wantedXL_stored (LinkFrame.lean); colOf_wanted, seat_of_tree (LinkFrameView.lean).

Limits. The pairs are wantedX's (OnBytes/TypedOracleCompiler/Run/PlanQX.lean): that a description's declared groups
ask for these pairs, with these widths, is not said here. The widths of next's columns and of the
stored strings' columns are premises; the first is asked at every history. Nothing here says that a
verifier accepts. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkFrameView
import Johnson.Desc.Plain.OneChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open _root_.Iop (twoExternalStrings)
open _root_.Run.PQ (XO SgX storedKey xPos)
open TypedOracleCompiler.Run.PQ (RD wantedX wantedXL treeSh)
open VerifiableInference.Desc.Plain.One (lookY)

/-- A wanted pair stands under a stored string's key or under an own tree's number. -/
theorem wantedXL_key (a : ℕ) (all : List RD) (xs : List XO) : ∀ (i : ℕ) (ds : List RD)
    (Ds : List Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
    ∀ kx ∈ wantedXL a all xs i ds Ds, (∃ w, kx.1 = storedKey w) ∨ kx.1 < 2 ^ 16
  | _, [], _, _, _, h => by simp [wantedXL] at h
  | _, _ :: _, [], _, _, h => by simp [wantedXL] at h
  | i, d :: ds, D :: Ds, hop, kx, h => by
      unfold wantedXL at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨o, -, h⟩ := List.mem_flatMap.1 h
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
          exact .inl ⟨o.which, rfl⟩
        · obtain ⟨n, hn, h⟩ := List.mem_flatMap.1 h
          split at h
          · cases h
          · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
            exact .inr (hop d List.mem_cons_self n hn)
      · exact wantedXL_key a all xs (i + 1) ds Ds
          (fun d' hd => hop d' (List.mem_cons_of_mem _ hd)) kx h

theorem key_le (w : Bool) : 2 ^ 16 ≤ storedKey w := Nat.le_add_right _ _

/-- **EVERY COLUMN THAT THE DRAWS ASK FOR IS THERE, WITH ITS WIDTH.** -/
theorem look_wanted (next : ℕ → List Fmt.Drawn → MsgV) (ds : List RD) (a : ℕ) (xs : List XO)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn) (W : Bool → ℕ)
    (hop : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) (hl : Ds.length = ds.length)
    (hW : ∀ j k d s, ds[j]? = some d → d.trees[k]? = some s →
      ∀ h x, ((next j h).col k x).length = s.W)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ a),
      ((twoExternalStrings (2 ^ a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = W w)
    (kx : ℕ × ℕ) (hk : kx ∈ wantedX a ds xs Ds) :
    ∃ c, lookY a y (colOf ds 0 [] next Ds) kx.1 kx.2 = some c ∧
      (∀ w, kx.1 = storedKey w → c.length = W w) ∧
      ∀ s, kx.1 < 2 ^ 16 → treeSh ds kx.1 = some s → c.length = s.W := by
  rcases wantedXL_key a ds xs 0 ds Ds hop kx hk with ⟨w, e⟩ | ho
  · have hge : 2 ^ 16 ≤ kx.1 := e ▸ key_le w
    have hlt := wantedXL_stored a ds xs 0 ds Ds hop kx hk hge
    have hx : ∀ b : Bool, xPos (2 ^ a) (b, kx.2) =
        some (if b then .inr ⟨kx.2, hlt⟩ else .inl ⟨kx.2, hlt⟩) := fun b => by
      unfold xPos
      rw [dif_pos hlt]
    have hkeys : storedKey false ≠ storedKey true := by decide
    unfold lookY
    cases w
    · rw [if_pos e, hx false]
      refine ⟨_, rfl, fun w' e' => ?_, fun s h _ => absurd hge (Nat.not_le.2 h)⟩
      cases w'
      · exact hy false kx.2 hlt
      · exact absurd (e.symm.trans e') hkeys
    · have hne : kx.1 ≠ storedKey false := fun e' => hkeys (e'.symm.trans e)
      rw [if_neg hne, if_pos e, hx true]
      refine ⟨_, rfl, fun w' e' => ?_, fun s h _ => absurd hge (Nat.not_le.2 h)⟩
      cases w'
      · exact absurd e' hne
      · exact hy true kx.2 hlt
  · have n0 : kx.1 ≠ storedKey false := fun e => absurd (e ▸ key_le false) (Nat.not_le.2 ho)
    have n1 : kx.1 ≠ storedKey true := fun e => absurd (e ▸ key_le true) (Nat.not_le.2 ho)
    obtain ⟨j, k, hs, hc⟩ := colOf_wanted next ds a xs Ds kx hk ho hl hW
    unfold lookY
    rw [if_neg n0, if_neg n1, hc]
    refine ⟨_, rfl, fun w e => absurd (e ▸ key_le w) (Nat.not_le.2 ho), fun s _ ht => ?_⟩
    obtain ⟨j', k', d, h1, h2, h3⟩ := seat_of_tree ds kx.1 s ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans h1))
    exact hW j k d s h2 h3 _ _

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.wantedXL_key
#print axioms Johnson.Prover.Link.key_le
#print axioms Johnson.Prover.Link.look_wanted

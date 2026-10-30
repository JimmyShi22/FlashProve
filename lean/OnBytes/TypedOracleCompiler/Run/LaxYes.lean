-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LaxYes.lean: WHEN THE LAX COMPILED VERIFIER SAYS YES UNDER ORACLE FUNCTIONS: ITS
CLAUSES ONE BY ONE, AND THOSE OF THEM THAT FOLLOW FROM THE WIRING's LAWS ALONE. General in the
protocol Q. Lemmas with proofs. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.
WHY (the record LaxYes (written in a file of this project that is not in this library) is at a
written protocol Z; the
entry's skeleton PSXE and the
batch's BatchPS are plain Q := P.up). afterB asks of the checks: (1) checksB | checksExt are some;
(2) at most nOpen checks; (3) each well formed AND of depth ≤ maxDepth; (4) each says yes.
  Run/WholePaths.lean gives (4) and the first half of (3).
  verifyB_yes            the chain yields (ρ, rts, ph); own | ext are some a | b; few; formed; every
                         check says yes (runCheckF); reqPartF; accept ⇒ (verifyB t Q wq …).det g =
                         true
  checksComp_isSome … checksB_isSome, checksExt_isSome     (1) FROM "EVERY READ POSITION HAS AN
                                                           OPENING"
  goodAt_depth, checksB_depth, checksExt_depth          the second half of (3): from RoundsQueryLayout.DepthLe
                                                        (a clause of wq.OKG); an external check has
                                                        the wire's depth
  comp_ps, trees_ps, opt_ps, checksB_ps                 to the checks of a string belongs a list
                                                        WITHOUT REPEATS of as many read positions:
                                                        from the wires' laws place_posAt0 |
                                                        place_posAtJ (a position names its
                                                        component, tree and leaf)
  length_checksB_le, length_checksExt_le            so there are at most as many checks as members
                                                    of any set that holds all read positions
  few_of_okg             (2): wq.OKG ⇒ (a ++ b).length ≤ wq.nOpen, at afterB's own tests of reading
  formed_of_okg          (3) whole: all well formed, wq.OKG, the external wire's depth ≤ maxDepth ⇒
                         afterB's clause
WHAT IS NOT SAID. That a read position has an opening; that a check says yes; the chain; the
decision. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.LaxDet
import OnBytes.TypedOracleCompiler.Run.WholePaths

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The clauses together -/

/-- The lax verifier's yes, from its clauses. -/
theorem verifyB_yes (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L)) {Y : Type}
    {E : ExtSpec} (t : Tag)
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (a b : List (Check lam L))
    (chain : (recomputeChainOfProof t Q wq embP xin cms x π).det g = some (ρ, rts, ph))
    (own : (haveI := wq.decO; checksB Q.loc.shape Q.ann wq.sh embS rts
      (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains)))
          π.opens) = some a)
    (ext : (haveI := wq.ext.dec; TypedOracleCompiler.Compile.Batch.checksExt wq.ext embE cms
      (fun p => decide (p ∈ Q.loc.extReads x ρ)) π.ext wq.ext.all) = some b)
    (few : (a ++ b).length ≤ wq.nOpen)
    (formed : (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true)
    (walks : (a ++ b).all (runCheckF g) = true) (req : reqPartF g depthReq π ph = true)
    (accept : Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens) = true) :
    (verifyB t Q wq embS embP xin embE depthReq cms x π).det g = true := by
  unfold verifyB
  rw [OComp.det_bind, chain]
  show (afterB Q wq embS embE depthReq cms x π ρ rts ph).det g = true
  rw [afterB_det]
  unfold afterBF
  simp only [own, ext]
  rw [if_pos ⟨few, formed⟩, walks, req, accept]
  rfl

/-! ## (1) Every read position has an opening -/

theorem checksComp_isSome {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig lam) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ p, isRead p = true → (f p).isSome = true) :
    ∀ js : List ℕ, (checksComp posAt depth emb rt isRead f js).isSome = true
  | [] => rfl
  | j :: js => by
      have ih := checksComp_isSome posAt depth emb rt isRead f h js
      obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 ih
      simp only [checksComp]
      split
      · rename_i p hp
        split_ifs with hr
        · obtain ⟨op, hop⟩ := Option.isSome_iff_exists.1 (h p hr)
          rw [hop, hcs]
          rfl
        · exact ih
      · exact ih

theorem checksTrees_isSome {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ p, isRead p = true → (f p).isSome = true) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)), (checksTrees posAt emb isRead f k ds
        rt).isSome = true
  | _, [], _ => by simp only [checksTrees]; rfl
  | _, _ :: _, [] => by simp only [checksTrees]; rfl
  | k, d :: ds, c :: rt => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1
        (checksComp_isSome (posAt k) d emb c isRead f h (List.range (2 ^ d)))
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (checksTrees_isSome posAt emb isRead f h
          (k + 1) ds rt)
      simp only [checksTrees, ha, hb]
      rfl

theorem checksOpt_isSome {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
        (h : ∀ p, isRead p = true → (f p).isSome = true) :
    (checksOpt posAt depth emb rt isRead f).isSome = true := by
  unfold checksOpt
  rw [Option.isSome_map]
  exact checksTrees_isSome posAt emb isRead f h 0 depth rt

/-- The checks of the protocol's own trees are there. -/
theorem checksB_isSome : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (emb : (p : OPos s) → OSym s p → Body L)
    (rts : RootsOfChain lam s) (isRead : OPos s → Bool) (f : (p : OPos s) → Option (Opening lam (OSym s p))),
    (∀ p, isRead p = true → (f p).isSome = true) → (checksB s A W emb rts isRead f).isSome = true
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f, h => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (checksOpt_isSome w.posAt0 w.depth0
          (fun p => emb (.inl p))
        (rt.1.getD []) (fun p => isRead (.inl p)) (fun p => f (.inl p)) fun p => h (.inl p))
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (checksOpt_isSome w.posAtJ w.depthJ
          (fun p => emb (.inl p))
        (rt.2.getD []) (fun p => isRead (.inl p)) (fun p => f (.inl p)) fun p => h (.inl p))
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (checksB_isSome s A W (fun p => emb (.inr p)) rts
        (fun p => isRead (.inr p)) (fun p => f (.inr p)) fun p => h (.inr p))
      simp only [checksB, ha, hb, hc]
      rfl

/-- The checks of the external trees are there. -/
theorem checksExt_isSome {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym))
    (h : ∀ p, isRead p = true → (f p).isSome = true) :
    ∀ ps : List E.Pos, (TypedOracleCompiler.Compile.Batch.checksExt we emb cms isRead f ps).isSome = true
  | [] => rfl
  | p :: ps => by
      have ih := checksExt_isSome we emb cms isRead f h ps
      obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 ih
      simp only [TypedOracleCompiler.Compile.Batch.checksExt]
      split_ifs with hr
      · obtain ⟨op, hop⟩ := Option.isSome_iff_exists.1 (h p hr)
        rw [hop, hcs]
        rfl
      · exact ih

/-! ## (3), its second half: depths -/

theorem goodAt_depth (n : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (emb : (p : OPos s) → OSym s p → Body L) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
    (f : (p : OPos s) → Option (Opening lam (OSym s p))),
    RoundsQueryLayout.DepthLe n s A W → GoodAt (fun c : Check lam L => c.depth ≤ n) s A W emb rts isRead f
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), _, (_, rts), _, _, h =>
    ⟨fun _ d _ hd _ _ _ _ _ _ _ _ => h.1.1 d (List.mem_of_getElem? hd),
      fun _ d _ hd _ _ _ _ _ _ _ _ => h.1.2 d (List.mem_of_getElem? hd),
      goodAt_depth n s A W _ rts _ _ h.2⟩

/-- No check of an own tree is deeper than the wiring allows. -/
theorem checksB_depth (n : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (emb : (p : OPos s) → OSym s p → Body L)
    (rts : RootsOfChain lam s) (isRead : OPos s → Bool) (f : (p : OPos s) → Option (Opening lam (OSym s p)))
    (h : RoundsQueryLayout.DepthLe n s A W) (cs : List (Check lam L))
        (e : checksB s A W emb rts isRead f = some cs) :
    ∀ c ∈ cs, c.depth ≤ n :=
  checksB_all (fun c : Check lam L => c.depth ≤ n) s A W emb rts isRead f
      (goodAt_depth n s A W emb rts isRead f h) cs e

theorem checksExt_depth {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) (ps : List E.Pos)
        (cs : List (Check lam L))
    (e : TypedOracleCompiler.Compile.Batch.checksExt we emb cms isRead f ps = some cs) : ∀ c ∈ cs,
        c.depth = we.depth :=
  checksExt_all (fun c : Check lam L => c.depth = we.depth) we emb cms isRead f
      (fun _ _ _ _ => rfl) ps cs e

/-! ## (2) As many checks as read positions -/

/-- one tree -/
theorem comp_ps {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig lam) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (place : r.Pos → ℕ) (hpl : ∀ j p, posAt j = some p → place p = j) :
    ∀ (js : List ℕ), js.Nodup → ∀ cs, checksComp posAt depth emb rt isRead f js = some cs →
      ∃ ps : List r.Pos, ps.Nodup ∧ ps.length = cs.length ∧ ∀ p ∈ ps, isRead p = true ∧ ∃ j ∈ js,
          posAt j = some p
  | [], _, cs, h => by
      obtain rfl : [] = cs := Option.some.inj h
      exact ⟨[], List.nodup_nil, rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | j :: js, hn, cs, h => by
      have up : ∀ cs', checksComp posAt depth emb rt isRead f js = some cs' →
          ∃ ps : List r.Pos, ps.Nodup ∧ ps.length = cs'.length ∧
            ∀ p ∈ ps, isRead p = true ∧ ∃ j' ∈ j :: js, posAt j' = some p := fun cs' h' => by
        obtain ⟨ps, h1, h2, h3⟩ := comp_ps posAt depth emb rt isRead f place hpl js
            (List.nodup_cons.1 hn).2 cs' h'
        exact ⟨ps, h1, h2, fun p hp => ⟨(h3 p hp).1, by
          obtain ⟨j', hj', e⟩ := (h3 p hp).2
          exact ⟨j', List.mem_cons_of_mem _ hj', e⟩⟩⟩
      simp only [checksComp] at h
      split at h
      · rename_i p hp
        split_ifs at h with hr
        · split at h
          · rename_i op cs' hop hcs
            obtain rfl := Option.some.inj h
            obtain ⟨ps, h1, h2, h3⟩ :=
              comp_ps posAt depth emb rt isRead f place hpl js (List.nodup_cons.1 hn).2 cs' hcs
            refine ⟨p :: ps, List.nodup_cons.2 ⟨fun hmem => ?_, h1⟩,
                by rw [List.length_cons, List.length_cons, h2],
              fun q hq => ?_⟩
            · obtain ⟨j', hj', e⟩ := (h3 p hmem).2
              have : j' = j := (hpl j' p e).symm.trans (hpl j p hp)
              exact (List.nodup_cons.1 hn).1 (this ▸ hj')
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact ⟨hr, j, List.mem_cons_self, hp⟩
              · obtain ⟨j', hj', e⟩ := (h3 q hq).2
                exact ⟨(h3 q hq).1, j', List.mem_cons_of_mem _ hj', e⟩
          · cases h
        · exact up cs h
      · exact up cs h

/-- the trees of a component, from number k on -/
theorem trees_ps {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (tree place : r.Pos → ℕ) (hpl : ∀ k j p, posAt k j = some p → tree p = k ∧ place p = j) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      ∃ ps : List r.Pos, ps.Nodup ∧ ps.length = (l.flatMap fun z => z.2.2).length ∧
        ∀ p ∈ ps, isRead p = true ∧ k ≤ tree p ∧ ∃ k' j, posAt k' j = some p
  | _, [], _, l, h => by
      simp only [checksTrees] at h
      obtain rfl := Option.some.inj h
      exact ⟨[], List.nodup_nil, rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | _, _ :: _, [], l, h => by
      simp only [checksTrees] at h
      obtain rfl := Option.some.inj h
      exact ⟨[], List.nodup_nil, rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | k, d :: ds, c :: rt, l, h => by
      simp only [checksTrees] at h
      cases h1 : checksComp (posAt k) d emb c isRead f (List.range (2 ^ d)) with
      | none => rw [h1] at h; cases h
      | some a =>
        cases h2 : checksTrees posAt emb isRead f (k + 1) ds rt with
        | none => rw [h1, h2] at h; cases h
        | some b =>
          rw [h1, h2] at h
          obtain rfl := Option.some.inj h
          obtain ⟨p1, n1, l1, m1⟩ := comp_ps (posAt k) d emb c isRead f place
              (fun j p e => (hpl k j p e).2)
            (List.range (2 ^ d)) List.nodup_range a h1
          obtain ⟨p2, n2, l2, m2⟩ := trees_ps posAt emb isRead f tree place hpl (k + 1) ds rt b h2
          refine ⟨p1 ++ p2, List.nodup_append.2 ⟨n1, n2, fun x hx y hy e => ?_⟩, ?_, fun p hp => ?_⟩
          · obtain ⟨j, -, ej⟩ := (m1 x hx).2
            have t1 : tree x = k := (hpl k j x ej).1
            have t2 : k + 1 ≤ tree y := (m2 y hy).2.1
            rw [← e, t1] at t2
            omega
          · rw [List.length_append, l1, l2, List.flatMap_cons, List.length_append]
          · rcases List.mem_append.1 hp with hp | hp
            · obtain ⟨j, -, ej⟩ := (m1 p hp).2
              exact ⟨(m1 p hp).1, le_of_eq (hpl k j p ej).1.symm, k, j, ej⟩
            · exact ⟨(m2 p hp).1, le_trans (Nat.le_succ k) (m2 p hp).2.1, (m2 p hp).2.2⟩

/-- All rounds: a list without repeats of as many read positions as there are checks. -/
theorem checksB_ps : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
    ∀ (emb : (p : OPos s) → OSym s p → Body L) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
      (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
      checksB s A W emb rts isRead f = some cs →
      ∃ ps : List (OPos s), ps.Nodup ∧ ps.length = cs.length ∧ ∀ p ∈ ps, isRead p = true
  | [], _, _, _, _, _, _, _, cs, h => by
      obtain rfl : [] = cs := Option.some.inj h
      exact ⟨[], List.nodup_nil, rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | _ :: s, (an, A), (w, W), hW, emb, (rt, rts), isRead, f, cs, h => by
      simp only [checksB] at h
      split at h
      · rename_i a b c ha hb hc
        obtain rfl := Option.some.inj h
        obtain ⟨la, hla, rfl⟩ := Option.map_eq_some_iff.1 ha
        obtain ⟨lb, hlb, rfl⟩ := Option.map_eq_some_iff.1 hb
        obtain ⟨p1, n1, l1, m1⟩ := trees_ps w.posAt0 (fun p => emb (.inl p))
            (fun p => isRead (.inl p))
          (fun p => f (.inl p)) w.tree w.place (fun k j p e => (hW.1.place_posAt0 k j p e).2) 0 _ _
              la hla
        obtain ⟨p2, n2, l2, m2⟩ := trees_ps w.posAtJ (fun p => emb (.inl p))
            (fun p => isRead (.inl p))
          (fun p => f (.inl p)) w.tree w.place (fun k j p e => (hW.1.place_posAtJ k j p e).2) 0 _ _
              lb hlb
        obtain ⟨p3, n3, l3, m3⟩ := checksB_ps s A W hW.2 (fun p => emb (.inr p)) rts
            (fun p => isRead (.inr p))
          (fun p => f (.inr p)) c hc
        have n12 : (p1 ++ p2).Nodup := List.nodup_append.2 ⟨n1, n2, fun x hx y hy e => by
          obtain ⟨k, j, ej⟩ := (m1 x hx).2.2
          obtain ⟨k', j', ej'⟩ := (m2 y hy).2.2
          have o1 := (hW.1.place_posAt0 k j x ej).1
          have o2 := (hW.1.place_posAtJ k' j' y ej').1
          rw [e, o2] at o1
          cases o1⟩
        refine ⟨(p1 ++ p2).map Sum.inl ++ p3.map Sum.inr,
          List.nodup_append.2 ⟨n12.map Sum.inl_injective, n3.map Sum.inr_injective,
              fun x hx y hy e => ?_⟩, ?_,
          fun p hp => ?_⟩
        · obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
          obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
          cases e
        · have e1 : (List.map Sum.inl (p1 ++ p2) ++ List.map Sum.inr p3 :
            List (_ ⊕ OPos s)).length =
              p1.length + p2.length + p3.length := by
            rw [List.length_append, List.length_map, List.length_map, List.length_append]
          have e2 : ((la.flatMap fun z => z.2.2) ++ (lb.flatMap fun z => z.2.2) ++ c).length =
              (la.flatMap fun z => z.2.2).length + (lb.flatMap fun z => z.2.2).length + c.length :=
                  by
            rw [List.length_append, List.length_append]
          exact e1.trans (by rw [e2, l1, l2, l3])
        · rcases List.mem_append.1 hp with hp | hp
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
            rcases List.mem_append.1 hq with hq | hq
            · exact (m1 q hq).1
            · exact (m2 q hq).1
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
            exact m3 q hq
      · cases h

/-- At most as many checks as members of a set that holds all read positions. -/
theorem length_checksB_le (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (hW : RoundsQueryLayout.OKG s A W)
    (emb : (p : OPos s) → OSym s p → Body L) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
    (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L))
    (h : checksB s A W emb rts isRead f = some cs) (R : Finset (OPos s))
        (hR : ∀ p, isRead p = true → p ∈ R) :
    cs.length ≤ R.card := by
  classical
  obtain ⟨ps, n, l, m⟩ := checksB_ps s A W hW emb rts isRead f cs h
  rw [← l, ← List.toFinset_card_of_nodup n]
  exact Finset.card_le_card fun p hp => hR p (m p (List.mem_toFinset.1 hp))

theorem length_checksExt_le {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L)
    (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos), ps.Nodup → ∀ (cs : List (Check lam L)),
      TypedOracleCompiler.Compile.Batch.checksExt we emb cms isRead f ps = some cs →
      ∀ (R : Finset E.Pos), (∀ p, isRead p = true → p ∈ R) → cs.length ≤ R.card := by
  classical
  have key : ∀ (ps : List E.Pos) (cs : List (Check lam L)),
      TypedOracleCompiler.Compile.Batch.checksExt we emb cms isRead f ps = some cs →
          cs.length = (ps.filter isRead).length := by
    intro ps
    induction ps with
    | nil =>
      intro cs h
      obtain rfl : [] = cs := Option.some.inj h
      rfl
    | cons p ps ih =>
      intro cs h
      simp only [TypedOracleCompiler.Compile.Batch.checksExt] at h
      split_ifs at h with hr
      · split at h
        · rename_i op cs' hop hcs
          obtain rfl := Option.some.inj h
          rw [List.filter_cons_of_pos hr, List.length_cons, List.length_cons, ih cs' hcs]
        · cases h
      · rw [List.filter_cons_of_neg hr]
        exact ih cs h
  intro ps hn cs h R hR
  rw [key ps cs h, ← List.toFinset_card_of_nodup (hn.filter _)]
  exact Finset.card_le_card fun p hp => hR p (List.mem_filter.1 (List.mem_toFinset.1 hp)).2

/-- (2): from the wiring's laws. -/
theorem few_of_okg {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (hq : wq.OKG)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
        (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (a b : List (Check lam L))
    (own : (haveI := wq.decO; checksB Q.loc.shape Q.ann wq.sh embS rts
      (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains)))
          π.opens) = some a)
    (ext : (haveI := wq.ext.dec; TypedOracleCompiler.Compile.Batch.checksExt wq.ext embE cms
      (fun p => decide (p ∈ Q.loc.extReads x ρ)) π.ext wq.ext.all) = some b) :
    (a ++ b).length ≤ wq.nOpen := by
  haveI := wq.decO
  haveI := wq.ext.dec
  rw [List.length_append]
  exact le_trans (Nat.add_le_add
    (length_checksB_le _ _ _ hq.sh embS rts _ _ a own
      (Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) fun p hp => by simpa using hp)
    (length_checksExt_le wq.ext embE cms _ _ wq.ext.all hq.ext.nodup b ext (Q.loc.extReads x ρ)
      fun p hp => by simpa using hp))
    (hq.opens x ρ _)

/-- (3) whole. -/
theorem formed_of_okg {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (hq : wq.OKG)
    (hd : wq.ext.depth ≤ wq.maxDepth)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
        (cms : List (Dig lam))
    (rts : RootsOfChain lam Q.loc.shape) (isRead : OPos Q.loc.shape → Bool) (isReadE : E.Pos → Bool)
        (π : OneProtocolProof lam Q)
    (a b : List (Check lam L)) (own : checksB Q.loc.shape Q.ann wq.sh embS rts isRead
        π.opens = some a)
    (ext : TypedOracleCompiler.Compile.Batch.checksExt wq.ext embE cms isReadE π.ext wq.ext.all = some b)
    (wf : (a ++ b).all (fun c => c.wellFormed) = true) :
    (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true :=
  List.all_eq_true.2 fun c hc => by
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.1 wf c hc, decide_eq_true ?_⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact checksB_depth wq.maxDepth _ _ _ embS rts isRead π.opens hq.depth a own c hc
    · rw [checksExt_depth wq.ext embE cms isReadE π.ext wq.ext.all b ext c hc]
      exact hd

end

end TypedOracleCompiler.Run

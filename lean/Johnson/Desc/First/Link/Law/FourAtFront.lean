-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FourAtFront.lean: AT THE BATCHING's FRONT OF A LINK: FROM WHAT THE
PREMISE hW OF `link_table_more` (LinkTableMore.lean) HANDS OUT TO "THE FIRST FOUR CLAIMS OF THE
APPROXIMATE RANGE PROOF's RUN ARE WORTH 0 IN THE BATCHING's OWN WORLD, AT THE LEDGER IN WHICH THE
ROWS' WEIGHTS ARE LAID". Theorems: a joining.

What is said.
  `four_at_front`: from: the link's duties (`JoinAsks` at the link's two rows of moves; RunOk of
    each run of the order); a yes of the batching's sub-protocol from a to b'; a yes of the moves
    behind the batching from b' to t; every term's coefficient 0 at the data y: t is full and has a
    part b; the run at the entry said yes at some state e of the gathering; e and t go on from what
    is fixed at a; t is later than the state behind the run; the first four claims of the run's list
    are worth 0 in `worldAt` at b's ledger, by `claimValue`. The draw and the moves' yes come out of
    the sub-protocol's yes as in Johnson/Desc/First/Batch/Law/Cores.lean's core1.
  `four_at_front_full`: the same at `Fu := FullAt nU` (GoodFull.lean), from the table's sentence
    "totalB" behind the batching: b's ledger is the library's `Fo.coefAll tlX g Fc`: SO THE END IS
    THE PREMISE hz OF THE EXCHANGE (k3Out_at_world, Johnson/Desc/First/K8/Four/AtWorld.lean)
    AND OF WHATEVER IS CUT FROM IT; with it: the run's yes as a yes of `equations`, handed the
    number of the ledger's claims plus those in front, AT A STRUCTURE tl THAT HAS HEARD THE SAME g
    and is tlX but for the fourteen written fields; AND THE THREE TIES (e and t go on from what is
    fixed at a; t is later than the state behind the run): without them e is pinned to nothing.

Limits. Implications. hFu4 (the entries' half of the four values) is taken as given, as in
Johnson/Desc/First/Batch/Law/K8Four.lean. The exchange itself is other files'. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTableMore
import Johnson.Desc.First.Link.Law.GoodFull
import Johnson.Desc.First.Link.Law.FullEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open _root_.Run (ckP)

variable {α W : Type} {F : Frame}

/-- **FROM A YES OF THE BATCHING's SUB-PROTOCOL AND OF THE MOVES BEHIND IT.** -/
theorem four_at_front (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (H : JoinAsks φ Ok Fu p pw (moves₁ L (rlOf L tmOf lenOf)) (moves₂ L) d N b₁ b₂ b₃ pb pq pe on0
      on1 on2 on3 tabOf ctx)
    (hrun : ∀ r ∈ rlOf L tmOf lenOf,
      RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) r.run.2 r.tm r.len)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (o : ℕ × String) (ho : o ∈ L.order) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y)
    (a : S × F.E.Str) (τ : _) (b' : S × F.E.Str) (ha : on0 a)
    (hout : pb.ior.red.out a τ = some b') (t : S)
    (hyt : MovesYes atS ((moves₂ (α := α) L).map (·.move)) b'.1 t []) (y : Bound GE8)
    (h0 : ∀ x ∈ termsRuns (fixed9 φ a.1) y (rlOf L tmOf lenOf) 0, x.2 = 0) :
    Fu t ∧ ∃ b front e ae c e₁, atS.get? t = some b ∧ Fx9 φ Ok (fixed9 φ a.1) e ∧
      Fx9 φ Ok (fixed9 φ a.1) t ∧ atS.get? e = some ae ∧ k8Run.2 front e = .ok (c, e₁) ∧
      laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t ∧
      ∀ k ∈ c.take 4, claimValue Reading.gl (worldAt Reading.gl b.L b.F y) k = 0 := by
  have HF := fitsM_atS (K := Cb.Gl.E) φ H.hφ Ok Fu p
  obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨_, x, a0, od, cls, _, _, ha0, hod, hy⟩ := H.hb₁ _ _ _ _ _ k hs
  obtain ⟨hfx, hgd⟩ := HF.atDraw a.1 a0 od x (H.hready a ha) ha0 hod
  obtain ⟨as, has, _, hsz⟩ := hgd
  have hgd' : good9 (atS.set a.1 { a0 with owed := od.owed, L := od.L, F := od.F }) :=
    (HF.atDraw a.1 a0 od x (H.hready a ha) ha0 hod).2
  have hyAll : MovesYes atS
      ((moves₁ L (rlOf L tmOf lenOf) ++ moves₂ (α := α) L).map (·.move))
      (atS.set a.1 { a0 with owed := od.owed, L := od.L, F := od.F }) t (cls ++ []) := by
    rw [List.map_append]
    exact movesYes_append atS _ _ _ _ _ _ _ hy hyt
  obtain ⟨hgt, hfull⟩ := H.hend _ t _ hgd' hyAll
  obtain ⟨b, hb, _, _⟩ := hgt
  obtain ⟨front, e, ae, c, e₁, f1, f2, h1, h2, hl, h3⟩ :=
    four_at_link L φ H.hφ Ok Fu p tmOf lenOf hrun H.hms u π hπ hkeep ent hOk4 hFu4 o ho run hAt hu
      ht (fixed9 φ a.1) _ t (cls ++ []) as hfx hgd' has hsz hyAll hfull b hb y h0
  exact ⟨hfull, b, front, e, ae, c, e₁, hb, f1, f2, h1, h2, hl, h3⟩

/-- **THE SAME AT `FullAt nU`, FROM THE TABLE's SENTENCE BEHIND THE BATCHING.** -/
theorem four_at_front_full (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (H : JoinAsks φ Ok (FullAt nU) p pw (moves₁ L (rlOf L tmOf lenOf)) (moves₂ L) d N b₁ b₂ b₃ pb
      pq pe on0 on1 on2 on3 tabOf ctx)
    (hrun : ∀ r ∈ rlOf L tmOf lenOf,
      RunOk Reading.gl atS (O9 φ Ok (FullAt nU)) (Fx9 φ Ok) r.run.2 r.tm r.len)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → FullAt nU t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (o : ℕ × String) (ho : o ∈ L.order) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (a : S × F.E.Str) (τ : _) (b' : S × F.E.Str) (ha : on0 a)
    (hout : pb.ior.red.out a τ = some b')
    (hB : totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own b'.1 rd) (y : Bound GE8)
    (h0 : ∀ x ∈ termsRuns (fixed9 φ a.1) y (rlOf L tmOf lenOf) 0, x.2 = 0) :
    ∃ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g : Forest.Heard) (front : ℕ) (e : S)
      (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork) (c : List Claim),
      K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t ∧ atS.get? t = some b ∧
      k8Tests nU e' = .ok t ∧ e'.fork? = some Fc ∧ e'.tl? = some tlX ∧ tlX.heard = some g ∧
      b.F = Fo.coefAll tlX g Fc ∧ e.fork? = some Fe ∧ e.tl? = some tl ∧ e.funs? = some funs ∧
      blank u tl = blank u tlX ∧ tl.heard = some g ∧
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) ∧
      Fx9 φ Ok (fixed9 φ a.1) e ∧ Fx9 φ Ok (fixed9 φ a.1) t ∧
      laterK atS (O9 (K := GE8) φ Ok (FullAt nU)) ((e.putTl tl').putFork F1) t ∧
      ∀ k ∈ c.take 4,
        claimValue Reading.gl (worldAt Reading.gl b.L (Fo.coefAll tlX g Fc) y) k = 0 := by
  obtain ⟨t, hta, _, _⟩ := hB
  have hq₂ : ∀ m ∈ (moves₂ (α := α) L).map (·.move), ∃ h, m = .quiet h := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.quiet q hq
  obtain ⟨hfull, b, front, e, ae, c, e₁, hb, fe, ft, _, hk, hl, hz⟩ :=
    four_at_front L φ Ok (FullAt nU) p pw tmOf lenOf d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx
      H hrun u π hπ hkeep ent hOk4 hFu4 o ho run hAt hu ht a τ b' ha hout t
      ((after_iff _ hq₂ b'.1 t).2 hta) y h0
  obtain ⟨e', hT⟩ := hfull
  obtain ⟨Fc, tlX, g, h1, h2, h3, h4, h5⟩ := k8_tests_coefAll nU e' t hT
  have eF : b.F = Fo.coefAll tlX g Fc := Option.some.inj ((K9.get_fork t b hb).symm.trans h5)
  obtain ⟨Fe, tl, funs, tl', F1, k1, k2, k3, k4, rfl⟩ := k8Run_ok front e e₁ c hk
  have htl : t.tl? = some tlX := by
    have hb' := hb
    rw [h4] at hb'
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 (part_back e' tlX _ b hb')
    obtain ⟨_, _, _, _, _, f4, _, _⟩ := get_put e' a' ha' tlX (Fo.coefAll tlX g Fc)
    rw [h4]
    exact f4
  have hbl : blank u tl = blank u tlX := by
    have q1 : (π (fixed9 φ a.1).1).1 = some (blank u tl) := by
      rw [← fe.2.1, hπ, k2]
      rfl
    have q2 : (π (fixed9 φ a.1).1).1 = some (blank u tlX) := by
      rw [← ft.2.1, hπ, htl]
      rfl
    exact Option.some.inj (q1.symm.trans q2)
  have hgl : tl.heard = some g := by
    have e1 : (blank u tl).heard = (blank u tlX).heard := congrArg (·.heard) hbl
    exact (show tl.heard = tlX.heard from e1).trans h3
  have hz' : ∀ k ∈ c.take 4,
      claimValue Reading.gl (worldAt Reading.gl b.L (Fo.coefAll tlX g Fc) y) k = 0 := eF ▸ hz
  exact ⟨t, e', b, Fc, tlX, g, front, e, Fe, tl, tl', funs, F1, c, hta, hb, hT, h1, h2, h3, eF, k1,
    k2, k3, hbl, hgl, k4, fe, ft, hl, hz'⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.four_at_front
#print axioms VerifiableInference.Desc.LinkJoin.four_at_front_full

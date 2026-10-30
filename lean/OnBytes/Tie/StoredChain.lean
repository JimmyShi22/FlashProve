-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredChain.lean: the compiled verifier's chain, at a chain that opens stored tables.

The compiled verifier first recomputes the hash chain of a typed string. The library proves what
that chain yields in the plain case: no stored tables, the tag "onl" (Run/PageIsChain.lean). The
case with stored tables runs at another interface, at the tag "link", under two roots, and spells
another first query (Run/PlanQXRun.lean). This file carries the result over. The chain depends on
all of these only through the answers to its queries, and behind the first query the two cases'
answers are the same.

Main theorems: `chainP_congr`, `famX_round`, `famX_first`, `chainX`.
It claims nothing on soundness.
-/
import Run.PageIsProofs
import Run.PlanQXRun
import OnBytes.Tie.StoredRead

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- A round behind the first, unfolded, whatever `x` is. -/
theorem chainP_step {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ())))
    (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) (r : RS)
    (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo) (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts : List (Dig lam)) (pl : r.Plain) (pls : Plains (up Ss)) :
    chainP Lf g id none t cms x salt rtreq (r :: Ss) (r.lo, A) (w, W) embP i (.loc v) rts (pl, pls)
      = match takeRt w.hasJ rts with
        | some (rt, rts') =>
          (chainP Lf g id none t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
            (.loc (List.ofFn (g (OracleName.fb t) (⟨i, .f2 none v, rt, embP (.inl (.inr pl))⟩ :
                      FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2)) rts' pls).map
            fun z => ((w.chal (g (OracleName.fb t) (⟨i, .f2 none v, rt, embP (.inl (.inr pl))⟩ :
                      FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).1, z.1),
              ((none, some rt), z.2.1), z.2.2)
        | none => none := rfl

/-- The chain over local rounds (`allLo`), begun behind the first round, is the same at two
interfaces, tags, families of oracle functions and arguments `x`, if the two families agree on every
query that a local round can make. -/
theorem chainP_congr {I X I' X' : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (Lf' : Unit → BatchProtocol I' X')
    (g : Fam (spec lam K (Lf ()))) (g' : Fam (spec lam K (Lf' ()))) (t t' : Tag)
    (cms cms' : List (Dig lam)) (x : Option X) (x' : Option X') (salt salt' : Bits)
    (rtreq rtreq' : Dig lam) :
    ∀ (Ss : List RS) (W : RoundsQueryLayout lam K (up Ss) (allLo Ss))
      (embP : PlainPart (up Ss) (allLo Ss) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
      (embP' : PlainPart (up Ss) (allLo Ss) → PlainPart (Compile.Batch.shapeOf (Lf' ()) t') (annOf (Lf' ()) t'))
      (i : ℕ) (v : Bits) (rts : List (Dig lam)) (pls : Plains (up Ss)),
      (∀ j v rt z, (g (OracleName.fb t) (⟨j, .f2 none v, rt, embP z⟩ : FbIn lam (Lf ()) t) :
          (Fin K → Dig lam) × Dig lam)
        = (g' (OracleName.fb t') (⟨j, .f2 none v, rt, embP' z⟩ : FbIn lam (Lf' ()) t') :
          (Fin K → Dig lam) × Dig lam)) →
      chainP Lf g id none t cms x salt rtreq Ss (allLo Ss) W embP i (.loc v) rts pls
        = chainP Lf' g' id none t' cms' x' salt' rtreq' Ss (allLo Ss) W embP' i (.loc v) rts pls
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: Ss, (w, W), embP, embP', i, v, rts, (pl, pls), hq => by
      show chainP Lf g id none t cms x salt rtreq (r :: Ss) (r.lo, allLo Ss) (w, W) embP i (.loc v)
          rts (pl, pls)
        = chainP Lf' g' id none t' cms' x' salt' rtreq' (r :: Ss) (r.lo, allLo Ss) (w, W) embP' i
          (.loc v) rts (pl, pls)
      rw [chainP_step, chainP_step]
      cases takeRt w.hasJ rts with
      | none => rfl
      | some y =>
        obtain ⟨rt, rts'⟩ := y
        dsimp only
        rw [hq i v rt (.inl (.inr pl)),
          chainP_congr Lf Lf' g g' t t' cms cms' x x' salt salt' rtreq rtreq' Ss W
            (fun z => embP (.inr z)) (fun z => embP' (.inr z)) (i + 1) _ rts' pls
            (fun j v rt z => hq j v rt (.inr z))]

/-- The first round, with no root and no `x`, unfolded. -/
theorem chainP_first_none {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)
    (g : Fam (spec lam K (Lf ()))) (t : Tag) (cms : List (Dig lam)) (salt : Bits)
    (rtreq : Dig lam) (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (rts : List (Dig lam)) (pl : r.Plain) (pls : Plains (up Ss)) (hw : w.hasJ = false) :
    chainP Lf g id none t cms (none : Option X) salt rtreq (r :: Ss) (r.lo, A) (w, W) embP 0 .first
        rts (pl, pls) =
      (chainP Lf g id none t cms (none : Option X) salt rtreq Ss A W (fun z => embP (.inr z)) 1
        (.loc (List.ofFn (g (OracleName.fb t) (⟨0, .f1 cms none salt, none, embP (.inl (.inr pl))⟩ :
                  FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2)) rts pls).map
        fun z => ((w.chal (g (OracleName.fb t) (⟨0, .f1 cms none salt, none, embP (.inl (.inr pl))⟩ :
                  FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).1, z.1),
          ((none, some none), z.2.1), z.2.2) := by
  show (match takeRt w.hasJ rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [hw]
  rfl

section
variable (D : XD) (dec : View → Bool)

/-- Behind the first query, the typed chain functions of the case with stored tables are those of
the plain case. -/
theorem famX_round (O : ByteArray → ByteArray) (j : ℕ) (v : Bits) (rt : Option (Dig 256))
    (z : PlainPart (uL D.C D.ds) (allLo (SL D.C D.ds))) :
    (Run.famOf O (PDS D.base D.C dec) (D.K + 1) (.fb .onl)
        (⟨j, .f2 none v, rt, embPS D.C D.ds dec (.inr z)⟩ :
          FbIn 256 (LbS D.C D.ds dec) .onl) : (Fin (D.K + 1) → Dig 256) × Dig 256)
      = (famX D dec O (D.K + 1) (.fb .link)
        (⟨j, .f2 none v, rt, embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, []))
          (fun _ => some ()) (.inr z)⟩ : FbIn 256 (D.L dec) .link) :
          (Fin (D.K + 1) → Dig 256) × Dig 256) := by
  cases j <;> rfl

/-- In the case with stored tables, the chain value in the typed answer to the first query is O's
answer at the format's first call, with the parameters' digest and `stm` of the two roots. -/
theorem famX_first (O : ByteArray → ByteArray) (cm cm' : Dig 256) (salt : Bits)
    (rt : Option (Dig 256))
    (pl : PlainPart (Compile.Batch.shapeOf (D.L dec) .link) (annOf (D.L dec) .link)) :
    (famX D dec O (D.K + 1) (.fb .link)
        (⟨0, .f1 [cm, cm'] none salt, rt, pl⟩ : FbIn 256 (D.L dec) .link) :
          (Fin (D.K + 1) → Dig 256) × Dig 256).2 =
      bytesToDig (O (Fmt.oStr 0 160 0 D.base.label Fmt.zero32
        (Run.firstBytes (Fmt.paramsDigest D.base.params)
          (D.stm (digToBytes cm) (digToBytes cm')) salt))) := by
  show ansOf O (if (Fin.last (D.K + 1)).val = D.K + 1 then some ⟨0, 160, 0, D.base.label,
    Fmt.zero32, Run.firstBytes (Fmt.paramsDigest D.base.params)
      (D.stm (digToBytes cm) (digToBytes cm')) salt⟩ else none) = _
  rw [if_pos (Fin.val_last (D.K + 1))]
  rfl

/-- The compiled verifier's chain at the tag "link", on the run value, roots and plain parts of a
chain output o. It yields what the plain case's chain yields: the draws of o's rounds, and work that
passes exactly if o's does. The hypotheses: O's answers, r0 and r1 have 32 bytes; the own part is
within the library's limits; the statement is `D.stm r0 r1`; o has `LaxFacts` and a run value, and
its `pd` is `Fmt.paramsDigest` of the parameters; pl types its plain parts. -/
theorem chainX (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (r0 r1 : ByteArray)
    (hok : PQ.ok D.base = true)
    (hst : D.base.statement = D.stm r0 r1) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (o : Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds))
    (hL : LaxFacts (Fmt.HO O) D.base o) (hpd : o.pd = Fmt.paramsDigest D.base.params)
    (hrun : o.run = some run) (hpl : plainsSL D.C D.ds o.rounds.toList = some pl) :
    ∃ (ρ : Rho (uL D.C D.ds)) (v : Bits),
      chainP (fun _ => D.L dec) (famX D dec O (D.K + 1)) id none .link
          [bytesToDig r0, bytesToDig r1] (none : Option Unit) (bytesToBits run) (fun _ => false)
          (SOf D.C D.ds) (allLo (SOf D.C D.ds))
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())) 0 .first
          ((rootsB o).map bytesToDig) ((), pl)
        = some ((default, ρ), ((none, some none), rtSL D.C D.ds o.rounds.toList), .loc v) ∧
      drawnSL D.C D.ds ρ = o.rounds.toList.map (·.drawn) ∧
      passSL D.C D.ds ρ
        = passL (Fmt.HO O) D.base.rounds o.rounds.toList ⟨D.base.label, o.rho0, 0⟩ := by
  obtain ⟨ρ, v, hc, hd, hp⟩ := pi_chain O hO D.base D.C D.K
    (chalP D.base.plan.field D.K) dec hok (kit_pull _ _) (room_kOf D.base) o run pl hL hrun hpl
  refine ⟨ρ, v, ?_, hd, hp⟩
  rw [← hc]
  have hpd32 : o.pd.size = 32 := by
    rw [hL.pd]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  have htail : (famX D dec O (D.K + 1) (.fb .link)
        (⟨0, .f1 [bytesToDig r0, bytesToDig r1] none (bytesToBits run), none,
          embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())
            (.inl (.inr ()))⟩ : FbIn 256 (D.L dec) .link) : (Fin (D.K + 1) → Dig 256) × Dig 256).2
      = (Run.famOf O (PDS D.base D.C dec) (D.K + 1) (.fb .onl)
        (⟨0, .f1 [bytesToDig o.pd] (some ()) (bytesToBits run), none,
          embPS D.C D.ds dec (.inl (.inr ()))⟩ : FbIn 256 (LbS D.C D.ds dec) .onl) :
          (Fin (D.K + 1) → Dig 256) × Dig 256).2 := by
    rw [famX_first, famOf_first, TieTree.dig_bytes _ h0, TieTree.dig_bytes _ h1,
      TieTree.dig_bytes _ hpd32, hpd, ← hst]
    rfl
  refine (chainP_first_none (fun _ => D.L dec) (famX D dec O (D.K + 1)) .link
    [bytesToDig r0, bytesToDig r1] (bytesToBits run) (fun _ => false) (s0 D.C) (SL D.C D.ds)
    (allLo (SL D.C D.ds)) (wire0S D.C D.K (chalP D.base.plan.field D.K))
    (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
    ((rootsB o).map bytesToDig) () pl rfl).trans ?_
  refine Eq.trans ?_ (chainP_first (y := ()) (fun _ => LbS D.C D.ds dec)
    (Run.famOf O (PDS D.base D.C dec) (D.K + 1)) .onl [bytesToDig o.pd]
    (bytesToBits run) (fun _ => false) (s0 D.C) (SL D.C D.ds) (allLo (SL D.C D.ds))
    (wire0S D.C D.K (chalP D.base.plan.field D.K))
    (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds) (embPS D.C D.ds dec)
    ((rootsB o).map bytesToDig) () pl rfl).symm
  have hcong := chainP_congr (fun _ => D.L dec) (fun _ => LbS D.C D.ds dec)
    (famX D dec O (D.K + 1)) (Run.famOf O (PDS D.base D.C dec) (D.K + 1))
    .link .onl [bytesToDig r0, bytesToDig r1] [bytesToDig o.pd] none (some ()) (bytesToBits run)
    (bytesToBits run) (fun _ => false) (fun _ => false) (SL D.C D.ds)
    (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (fun z => embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()) (.inr z))
    (fun z => embPS D.C D.ds dec (.inr z)) 1
    (List.ofFn (Run.famOf O (PDS D.base D.C dec) (D.K + 1) (.fb .onl)
        (⟨0, .f1 [bytesToDig o.pd] (some ()) (bytesToBits run), none,
          embPS D.C D.ds dec (.inl (.inr ()))⟩ : FbIn 256 (LbS D.C D.ds dec) .onl) :
          (Fin (D.K + 1) → Dig 256) × Dig 256).2)
    ((rootsB o).map bytesToDig) pl (fun j v rt z => (famX_round D dec O j v rt z).symm)
  rw [htail]
  rw [hcong]
  refine congrArg (fun f => Option.map f _) (funext fun z => ?_)
  exact congrArg (fun c => ((c, z.1), ((none, some none), z.2.1), z.2.2)) (Subsingleton.elim _ _)

end

end OnBytes.Tie

#print axioms OnBytes.Tie.chainP_congr
#print axioms OnBytes.Tie.chainX

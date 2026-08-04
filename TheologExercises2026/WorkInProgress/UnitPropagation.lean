import TheologExercises2026.Exercises.Exercise04

theorem HornFormula.sat_iff_unit_sat [DecidableEq Atom] (H : HornFormula Atom) (L : HornClause Atom) : H.toFormula.satisfiable ↔ (H.unit L).toFormula.satisfiable := by
  unfold Formula.satisfiable
  constructor
  . intro sat
    rcases sat with ⟨v, v_sat⟩
    exists v
    unfold unit
    rw [eval_toFormula_eq] at *
    by_cases L_mem : L ∈ H
    . simp only [L_mem, if_true]
      . split
        -- neg. unit clause
        next hd body p hd_eq body_eq =>
          simp?
          intro C C_mem
          by_cases hC : C.body.contains p
          . apply Or.inl; grind
          . apply Or.inr
            have C_eval : v.eval C.toFormula = true := by grind
            simp at hC
            rw [HornClause.eval_true_iff] at C_eval
            have test := (HornClause.eval_true_iff (C.remove p) v).mpr
            rcases C_eval with ⟨q, hq⟩
            have aux : ∃ q, (C.remove p).head.isEqSome q = true ∧ v.eval (Formula.atom q) = true ∨ q ∈ (C.remove p).body ∧ v.eval (Formula.atom q) = false := by
              exists q
              apply Or.inr
              constructor
              .
                sorry
              . sorry


            --rcases C_eval with ⟨q, ⟨q_hd, q_eval⟩ | ⟨q_mem, q_eval⟩⟩

            sorry
        next hd body p hd_eq body_eq =>
          simp
          intro C C_mem
          by_cases hC : C.head == some p
          . apply Or.inl; grind
          . apply Or.inr
            simp only [Bool.not_eq_true] at hC
            have C_eval : v.eval C.toFormula := by grind
            have p_eval : v.eval (Formula.atom p) := by
              simp only [List.all_eq, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,decide_eq_true_eq] at v_sat
              specialize v_sat L L_mem
              unfold HornClause.toFormula at v_sat
              simp [hd_eq, body_eq, Formula.disjunction_from_list] at v_sat
              exact v_sat
            have not_p_eval : !v.eval (Formula.atom p).not := by grind
            have test := (HornClause.eval_true_iff C v).mp C_eval

            unfold HornClause.remove
            simp only [Option.isEqSome_eq_beq_some, hC, Bool.false_eq_true, ↓reduceIte]
            cases C_head : C.head with
            | none =>
              rcases test with ⟨q, ⟨q_hd, q_eval⟩ | ⟨q_mem, q_eval⟩⟩
              . grind
              . have q_mem' : q ∈ C.body.removeAll [p] := by grind
                rw [HornClause.eval_true_iff]
                exists q
                simp; exact ⟨q_mem', q_eval⟩
            | some r =>
              rcases test with ⟨q, ⟨q_hd, q_eval⟩ | ⟨q_mem, q_eval⟩⟩
              . unfold HornClause.toFormula Formula.disjunction_from_list
                simp only; grind
              . have q_mem' : q ∈ C.body.removeAll [p] := by grind
                rw [HornClause.eval_true_iff]
                exists q
                simp only [Option.isEqSome_eq_beq_some, Option.some_beq_some, beq_iff_eq]
                apply Or.inr
                exact ⟨q_mem', q_eval⟩
        . grind
    . simp only [L_mem, if_false]; grind

  . rintro ⟨v, v_eval⟩
    by_cases L_mem : L ∈ H
    . simp only [unit, L_mem, if_true] at v_eval
      split at v_eval
      next hd body p L_hd L_body =>
        let v' : Valuation Atom := fun x => if x == p then false else v x
        exists v'
        rw [eval_toFormula_eq] at *
        simp only [List.all_map, List.all_eq_true, Function.comp_apply] at *
        simp only [List.elem_eq_contains, List.contains_eq_mem, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, and_imp] at v_eval
        intro C C_mem
        by_cases p_mem : p ∈ C.body
        . rw [HornClause.eval_true_iff]
          exists p
          apply Or.inr
          constructor
          . exact p_mem
          . unfold v'
            grind
        . specialize v_eval C C_mem p_mem
          rw [HornClause.eval_true_iff] at v_eval
          have p_nmem : ¬p ∈ C.remove p := by
            unfold HornClause.remove Membership.mem HornClause.instMembership
            simp only [List.removeAll]
            simp only [Option.isEqSome_eq_beq_some, beq_iff_eq, Option.ite_none_left_eq_some, not_and_self, List.contains_eq_mem, List.not_mem_nil, or_false,
              List.decide_mem_cons, decide_false, Bool.or_false, List.mem_filter, BEq.rfl, Bool.not_true, Bool.false_eq_true, and_false, not_false_eq_true]
          have p_eval : v'.eval (Formula.atom p) = false := by grind
          rcases v_eval with ⟨q, v_eval⟩
          rcases v_eval with ⟨q_hd, q_eval⟩ | ⟨q_mem, q_eval⟩
          . rw [HornClause.eval_true_iff]
            exists q
            apply Or.inl
            constructor
            . unfold HornClause.remove at q_hd
              simp only [Option.isEqSome_eq_beq_some, beq_iff_eq, Option.ite_none_left_eq_some] at *
              exact q_hd.right
            . have q_mem : q ∈ C.remove p := by
                unfold Membership.mem HornClause.instMembership
                simp only [Option.isEqSome_eq_beq_some, beq_iff_eq] at q_hd
                apply Or.inl
                exact q_hd
              have q_neq : q ≠ p := by grind
              grind
          . rw [HornClause.eval_true_iff]
            exists q
            apply Or.inr
            constructor
            . unfold HornClause.remove at q_mem
              simp only at q_mem
              grind
            . grind
      next hd body p L_hd L_body =>
        let v' : Valuation Atom := fun x => if x == p then true else v x
        exists v'
        rw [eval_toFormula_eq] at *
        simp only [Option.isEqSome_eq_beq_some, List.map_map, List.all_map, List.all_filter, Bool.not_not, Function.comp_apply, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at *
        intro C C_mem

        sorry
      next => grind
    . simp only [unit, L_mem, if_false] at v_eval; exists v


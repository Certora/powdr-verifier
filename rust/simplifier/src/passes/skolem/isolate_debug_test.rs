#[cfg(test)]
mod isolate_body_head {
    use smt2::ast_util::{or_body_parts, or_parts, quantifier_body_bool};
    use smt2::Script;
    use z3::ast::{Ast, Dynamic};

    #[test]
    fn keccak_forall_body_shape() {
        let script = Script::parse_file(
            "/home/gereon/certora/powdr/verifier/data/guest-keccak-selection/verify-apc_candidate_2105892_035_inlining-apc_candidate_2105892_036_remove_disconnected.soundness.smt2",
        )
        .unwrap();
        let nnf = crate::passes::nnf::apply(&script).unwrap().0;
        let full = nnf
            .commands
            .iter()
            .find_map(|c| c.assert_bool())
            .unwrap();
        let body = quantifier_body_bool(&Dynamic::from_ast(full)).unwrap();
        let ast = Dynamic::from_ast(&body);
        let head = if ast.kind() == z3::ast::AstKind::App {
            smt2::ast_util::decl_name(&ast.decl())
        } else {
            format!("{:?}", ast.kind())
        };
        eprintln!("body head={head} or_parts={:?} or_body_parts={:?}", or_parts(&body).map(|v| v.len()), or_body_parts(&body).map(|v| v.len()));
        assert!(or_body_parts(&body).is_some(), "expected peelable or body, head={head}");
    }
}

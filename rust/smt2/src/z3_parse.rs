//! Z3 SMT-LIB parser context for ingesting commands.

use std::ffi::CString;

use z3::ast::{Ast, Bool};
use z3::Context;
use z3_sys::*;

pub struct ParseCtx {
    ctx: Context,
    pc: Z3_parser_context,
}

impl ParseCtx {
    pub fn new() -> Self {
        let ctx = Context::thread_local();
        unsafe {
            let z3 = ctx.get_z3_context();
            let pc = Z3_mk_parser_context(z3).expect("Z3_mk_parser_context");
            Z3_parser_context_inc_ref(z3, pc);
            Self { ctx, pc }
        }
    }

    pub fn context(&self) -> &Context {
        &self.ctx
    }

    /// Feed one complete top-level SMT-LIB command. Returns `Some(Bool)` for `assert`.
    pub fn ingest_command(&mut self, raw: &str) -> Result<Option<Bool>, String> {
        let cstr = CString::new(raw).map_err(|e| e.to_string())?;
        unsafe {
            let z3 = self.ctx.get_z3_context();
            let Some(av_ptr) = Z3_parser_context_from_string(z3, self.pc, cstr.as_ptr()) else {
                let code = Z3_get_error_code(z3);
                let msg = Z3_get_error_msg(z3, code);
                let err = if msg.is_null() {
                    format!("Z3 parser error (code {code:?})")
                } else {
                    std::ffi::CStr::from_ptr(msg)
                        .to_string_lossy()
                        .into_owned()
                };
                return Err(err);
            };
            Z3_ast_vector_inc_ref(z3, av_ptr);
            let n = Z3_ast_vector_size(z3, av_ptr);
            let mut out = None;
            for i in 0..n {
                let ast = Z3_ast_vector_get(z3, av_ptr, i).expect("ast_vector_get");
                let b = Bool::wrap(&self.ctx, ast);
                out = Some(b);
            }
            Z3_ast_vector_dec_ref(z3, av_ptr);
            Ok(out)
        }
    }
}

impl Drop for ParseCtx {
    fn drop(&mut self) {
        unsafe {
            Z3_parser_context_dec_ref(self.ctx.get_z3_context(), self.pc);
        }
    }
}

pub mod cancel;
pub mod circuit;
pub mod decompose;
pub mod pass;
pub mod phase_fold_global_expr;
pub mod phase_fold_rand;
pub mod qasm;
pub mod super_opt;

#[deprecated(note = "use tzap::super_opt instead")]
pub mod subcircuit_matrix {
    pub use crate::super_opt::{
        SuperOptError as SubcircuitMatrixError, SuperOpt as SubcircuitMatrixPass,
        SuperOptResult as SubcircuitMatrixResult, SuperOptRewrite as SubcircuitRewrite,
        SuperOptTableConfig as SubcircuitMatrixTableConfig, SuperOptWindow as SubcircuitMatrix,
    };
}

#[deprecated(note = "use tzap::super_opt instead")]
pub mod superopt {
    pub use crate::super_opt::*;
}

#[cfg(test)]
mod bench;
#[cfg(test)]
mod unitary;

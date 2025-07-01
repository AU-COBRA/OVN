use std::collections::HashSet;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface, Queries};
use rustc_span::symbol::Symbol;

use crate::callbacks_wrapper::CallbacksWrapper;

use serde::{Deserialize, Serialize};

/// A subset of `rustc_feature::Features` that is relevant to us
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Features {
    pub adt_const_params: bool,
    pub generic_const_exprs: bool,
    pub register_tool: bool,
    pub auto_traits: bool,
    pub negative_impls: bool,
    pub registered_tools: HashSet<String>,
}

impl From<&rustc_feature::Features> for Features {
    fn from(rfeatures: &rustc_feature::Features) -> Self {
        Features {
            adt_const_params: rfeatures.adt_const_params,
            generic_const_exprs: rfeatures.generic_const_exprs,
            register_tool: rfeatures.register_tool,
            auto_traits: rfeatures.auto_traits,
            negative_impls: rfeatures.negative_impls,
            registered_tools: HashSet::new(),
        }
    }
}

impl core::ops::Sub for Features {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        fn sub(x: bool, y: bool) -> bool {
            x & !y
        }
        Features {
            adt_const_params: sub(self.adt_const_params, rhs.adt_const_params),
            generic_const_exprs: sub(self.generic_const_exprs, rhs.generic_const_exprs),
            register_tool: sub(self.register_tool, rhs.register_tool),
            auto_traits: sub(self.auto_traits, rhs.auto_traits),
            negative_impls: sub(self.negative_impls, rhs.negative_impls),
            registered_tools: self
                .registered_tools
                .difference(&rhs.registered_tools)
                .cloned()
                .collect(),
        }
    }
}

impl Default for Features {
    fn default() -> Self {
        (&rustc_feature::Features::default()).into()
    }
}

impl Features {
    pub fn into_iter(&self) -> impl Iterator<Item = String> {
        [
            self.adt_const_params.then_some("adt_const_params"),
            self.generic_const_exprs.then_some("generic_const_exprs"),
            self.register_tool.then_some("register_tool"),
        ]
        .into_iter()
        .flatten()
        .map(|s| format!("feature({})", s))
        .chain(
            self.registered_tools
                .clone()
                .into_iter()
                .map(|tool| format!("register_tool({})", tool)),
        )
    }
    /// Runs Rustc with a driver that only collects which unstable
    /// Rustc features are enabled
    pub fn detect(options: &hax_types::cli_options::Options, rustc_args: &Vec<String>) -> Self {
        struct CollectFeatures {
            features: Features,
        }
        impl Callbacks for CollectFeatures {
            fn after_expansion<'tcx>(
                &mut self,
                compiler: &interface::Compiler,
                queries: &'tcx Queries<'tcx>,
            ) -> Compilation {
                queries.global_ctxt().unwrap().enter(|tcx| {
                    self.features = tcx.features().into();
                    self.features.registered_tools = tcx
                        .registered_tools(())
                        .iter()
                        .map(|x| x.name.to_ident_string())
                        .collect();
                });
                rustc_driver::Compilation::Stop
            }
        }
        let mut callbacks = CollectFeatures {
            features: Features::default(),
        };
        let exit_code = rustc_driver::catch_with_exit_code(|| {
            rustc_driver::RunCompiler::new(
                &rustc_args,
                &mut CallbacksWrapper {
                    sub: &mut callbacks,
                    options: options.clone(),
                },
            )
            .run()
        });
        if exit_code != 0 {
            std::process::exit(exit_code);
        }
        callbacks.features.clone()
    }

    /// Just like `detect`, but wraps the call in a subprocess so that
    /// we can capture `stdout` and `stderr`: we don't want the use to
    /// see error message from Rustc twice, or Cargo to have to parse
    /// Rustc messages twice.
    pub fn detect_forking() -> Self {
        use std::process::{Command, Stdio};
        let output = Command::new(std::env::args().next().unwrap())
            .args(std::env::args().skip(1))
            .env("HAX_FEATURES_DETECTION_MODE", "1")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap()
            .wait_with_output()
            .unwrap();
        let stderr = &std::str::from_utf8(&output.stderr).unwrap();
        serde_json::from_str(stderr).unwrap_or_else(|e| {
            eprintln!("{}", stderr);
            tracing::error!("rustc emitted an error, aborting hax custom driver.");
            std::process::exit(1);
        })
    }
}

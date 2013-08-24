(*

Copyright 2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

namespace Tests.NHol

/// Functions for manipulating the NHol system state to facilitate unit testing.
[<RequireQualifiedAccess>]
module internal SystemState =
    open System.Reflection
    open System.Runtime.CompilerServices


    /// Initializes NHol modules (F# modules), given a reference to the NHol assembly
    /// and a list of module names to initialize.
    let rec private initializeNHolModules (nholAssembly : Assembly) moduleNames =
        match moduleNames with
        | [] -> ()
        | moduleName :: moduleNames ->
            /// The full name (namespace + name) of the type containing the startup (initialization)
            /// code for the current NHol module (F# module).
            let moduleStartupTypeName = "<StartupCode$NHol>.$NHol." + moduleName

            // Try to get the F# module type from the map containing the types in the assembly.
            match nholAssembly.GetType (moduleStartupTypeName, false) |> Option.ofNull with
            | None ->
                // If the module's startup type couldn't be found, emit a message to the NUnit console/log.
                printfn "Unable to initialize the '%s' module because it could not be found in the NHol assembly. (ModuleStartupTypeName = %s)"
                    moduleName moduleStartupTypeName

            | Some moduleType ->
                // Emit a message to the NUnit console/log so we know which module we're initializing
                // in case something goes wrong during the initialization.
                printfn "Initializing the '%s' module." moduleName

                // Execute the static constructor (class constructor) for the class
                // representing the specified F# module.
                RuntimeHelpers.RunClassConstructor moduleType.TypeHandle

                // Emit a message to the NUnit console/log stating that the module was initialized.
                printfn "Initialized the '%s' module." moduleName

            // Initialize the remaining modules.
            initializeNHolModules nholAssembly moduleNames

    /// Initializes the NHol modules in the correct order.
    /// Used to avoid issues with out-of-order initialization when running unit tests.
    let initialize () =
        // Emit a message to the NUnit console/log to record that this function was called.
        printfn "Initializing NHol modules prior to running unit tests."

        /// The NHol assembly.
        let nholAssembly = typeof<NHol.fusion.Hol_kernel.hol_type>.Assembly

        // First initialize the module itself.
        // This isn't really necessary, since C# normally doesn't add anything to the
        // module constructor, but it doesn't hurt to be sure.
        printfn "Running the NHol module (.dll) constructor."
        RuntimeHelpers.RunModuleConstructor nholAssembly.ManifestModule.ModuleHandle
        
        // Now, initialize each of the F# modules in the NHol assembly by executing
        // the static constructor (.cctor) for the static class representing the module.
        // We use the same ordering as when loading the files into F# interactive,
        // so we should get the same results.
        initializeNHolModules nholAssembly
           ["lib";
            "fusion";
            "basics";
            "nets";
            "printer";
            "preterm";
            "parser";
            "equal";
            "bool";
            "drule";
            "tactics";
            "itab";
            "simp";
            "theorems";
            "ind_defs";
            "class";
            "trivia";
//            "canon";
//            "meson";
//            "quot";
//            "pair";
//            "nums";
//            "recursion";
//            "arith";
//            "wf";
//            "calc_num";
//            "normalizer";
//            "grobner";
//            "ind_types";
//            "lists";
//            "realax";
//            "calc_int";
//            "realarith";
//            "real";
//            "calc_rat";
//            "int";
//            "sets";
//            "iterate";
//            "cart";
//            "define";
//            "help";
//            "database";
            ]


/// Global setup/teardown for test fixtures in this project.
[<Sealed>]
[<NUnit.Framework.SetUpFixture>]
type NHolTestSetupFixture () =
    /// Forces the modules in the NHol assembly to be initialized in the correct order
    /// if they haven't been already. NUnit calls this method once prior to each test run.
    [<NUnit.Framework.SetUp>]
    member __.NHolTestsInit () =
        // Initialize the NHol modules in the correct order before running any tests.
        SystemState.initialize ()


/// Functions for resetting mutable state values within each
/// NHol module (F# module) to facilitate unit testing.
[<RequireQualifiedAccess>]
module ModuleReset =
    open NHol


    /// Emits a message to the NUnit log/console before and after executing an action
    /// function to reset the mutable state within a module.
    let inline private logModuleResetAction moduleName action =
        // Emit a message to the NUnit console/log to record that we're resetting this module.
        printfn "Resetting the mutable state in the '%s' module." moduleName

        // Execute the action to reset the module.
        action ()

        // Emit another message to the NUnit console/log to record we've finished resetting this module.
        printfn "Finished resetting the mutable state in the '%s' module." moduleName
    
    //
    let lib () =
        logModuleResetAction "lib" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'lib' module has not been implemented."

    //
    let fusion () =
        logModuleResetAction "fusion" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'fusion' module has not been implemented."

    //
    let basics () =
        logModuleResetAction "basics" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'basics' module has not been implemented."

    //
    let nets () =
        logModuleResetAction "nets" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'nets' module has not been implemented."

    //
    let printer () =
        logModuleResetAction "printer" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'printer' module has not been implemented."

    //
    let preterm () =
        logModuleResetAction "preterm" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'preterm' module has not been implemented."

    //
    let parser () =
        logModuleResetAction "parser" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'parser' module has not been implemented."

    //
    let equal () =
        logModuleResetAction "equal" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'equal' module has not been implemented."

    //
    let bool () =
        logModuleResetAction "bool" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'bool' module has not been implemented."

    //
    let drule () =
        logModuleResetAction "drule" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'drule' module has not been implemented."

    //
    let tactics () =
        logModuleResetAction "tactics" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'tactics' module has not been implemented."

    //
    let itab () =
        logModuleResetAction "itab" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'itab' module has not been implemented."

    //
    let simp () =
        logModuleResetAction "simp" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'simp' module has not been implemented."

    //
    let theorems () =
        logModuleResetAction "theorems" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'theorems' module has not been implemented."

    //
    let ind_defs () =
        logModuleResetAction "ind_defs" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'ind_defs' module has not been implemented."

    //
    let ``class`` () =
        logModuleResetAction "class" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'class' module has not been implemented."

    //
    let trivia () =
        logModuleResetAction "trivia" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'trivia' module has not been implemented."

    //
    let canon () =
        logModuleResetAction "canon" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'canon' module has not been implemented."

    //
    let meson () =
        logModuleResetAction "meson" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'meson' module has not been implemented."

    //
    let quot () =
        logModuleResetAction "quot" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'quot' module has not been implemented."

    //
    let pair () =
        logModuleResetAction "pair" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'pair' module has not been implemented."

    //
    let nums () =
        logModuleResetAction "nums" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'nums' module has not been implemented."

    //
    let recursion () =
        logModuleResetAction "recursion" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'recursion' module has not been implemented."

    //
    let arith () =
        logModuleResetAction "arith" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'arith' module has not been implemented."

    //
    let wf () =
        logModuleResetAction "wf" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'wf' module has not been implemented."

    //
    let calc_num () =
        logModuleResetAction "calc_num" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'calc_num' module has not been implemented."

    //
    let normalizer () =
        logModuleResetAction "normalizer" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'normalizer' module has not been implemented."

    //
    let grobner () =
        logModuleResetAction "grobner" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'grobner' module has not been implemented."

    //
    let ind_types () =
        logModuleResetAction "ind_types" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'ind_types' module has not been implemented."

    //
    let lists () =
        logModuleResetAction "lists" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'lists' module has not been implemented."

    //
    let realax () =
        logModuleResetAction "realax" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'realax' module has not been implemented."

    //
    let calc_int () =
        logModuleResetAction "calc_int" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'calc_int' module has not been implemented."

    //
    let realarith () =
        logModuleResetAction "realarith" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'realarith' module has not been implemented."

    //
    let real () =
        logModuleResetAction "real" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'real' module has not been implemented."

    //
    let calc_rat () =
        logModuleResetAction "calc_rat" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'calc_rat' module has not been implemented."

    //
    let int () =
        logModuleResetAction "int" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'int' module has not been implemented."

    //
    let sets () =
        logModuleResetAction "sets" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'sets' module has not been implemented."

    //
    let iterate () =
        logModuleResetAction "iterate" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'iterate' module has not been implemented."

    //
    let cart () =
        logModuleResetAction "cart" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'cart' module has not been implemented."

    //
    let define () =
        logModuleResetAction "define" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'define' module has not been implemented."

    //
    let help () =
        logModuleResetAction "help" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'help' module has not been implemented."

    //
    let database () =
        logModuleResetAction "database" <| fun () ->
            // TODO
            printfn "Warning : The resetting action for the 'database' module has not been implemented."


/// Helper functions for implementing setup functions for fixtures and tests.
[<RequireQualifiedAccess>]
module SetupHelpers =
    /// Emits a message to the NUnit console/log stating that the test fixture setup function
    /// is empty (i.e., does nothing), given the name of the NHol module tested by the fixture.
    let emitEmptyTestFixtureSetupMessage moduleName =
        printfn "Info : The test fixture setup function for the '%s' module is empty." moduleName

    /// Emits a message to the NUnit console/log stating that the mutable state will be reset
    /// in modules up to and including the specified module.
    let emitTestSetupModuleResetMessage moduleName =
        printfn "Resetting mutable state in modules up to and including the '%s' module." moduleName

module ProofGUI1

#r "System.Windows"
#r "WindowsBase"
#r "System.Xaml"
#r "PresentationCore"
#r "PresentationFramework"

open System.Xml
open System.Windows


open System.Windows.Media
open System.Windows.Markup
open System.Windows.Shapes
open System.Windows.Controls

#I "./../packages"

#r "FSharp.Compatibility.OCaml.0.1.10/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "FSharp.Compatibility.OCaml.Format.0.1.10/lib/net40/FSharp.Compatibility.OCaml.Format.dll"
#r "FSharp.Compatibility.OCaml.System.0.1.10/lib/net40/FSharp.Compatibility.OCaml.System.dll"
#r "ExtCore.0.8.33/lib/net40/ExtCore.dll"

#I "./../NHol"
#r @"bin/Debug/NHol.dll"

#nowarn "25"
#nowarn "40"
#nowarn "49"
#nowarn "62"

open FSharp.Compatibility.OCaml;;
open FSharp.Compatibility.OCaml.Num;;
open FSharp.Compatibility.OCaml.Format;;

open ExtCore.Control;;
open ExtCore.Control.Collections;;

open NHol
open NHol.lib
open NHol.fusion
open NHol.basics
open NHol.nets
open NHol.printer
open NHol.preterm
open NHol.parser
open NHol.equal
open NHol.bool
open NHol.drule
open NHol.tactics
open NHol.itab
open NHol.simp
open NHol.theorems
open NHol.ind_defs
open NHol.``class``
open NHol.trivia
open NHol.canon
open NHol.meson

let proofGUI() = 

    let loadXamlWindow (filename:string) =
      let reader = XmlReader.Create(filename)
      XamlReader.Load(reader) :?> Window

    let app = new Application()

    // Load the window.xaml file
    let w = loadXamlWindow(__SOURCE_DIRECTORY__ + @"\MainWindow.xaml")
    w.Show()

    // We assume that there is an button named btnExecute
    let btnExecute = w.FindName("btnExecute") :?> System.Windows.Controls.Button
    let txt1 = w.FindName("txt1") :?> System.Windows.Controls.TextBox
    let txt2 = w.FindName("txt2") :?> System.Windows.Controls.TextBox

    btnExecute
        .Click
        .Add(fun _ -> 
                let tm1str = txt1.Text
                let tm1 = parse_term tm1str
                let thm1 = ASSUME tm1
                txt2.Text <- string_of_thm (Choice.get <| thm1)
                ())
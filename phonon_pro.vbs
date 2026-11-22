' Phonon Studio Pro - silent launcher
' Hides the CMD window; runs phonon_pro.bat completely in the background.
' First run: double-click phonon_pro.bat instead (visible) so it can install and download.
Set fso = CreateObject("Scripting.FileSystemObject")
Set sh  = CreateObject("WScript.Shell")
here = fso.GetParentFolderName(WScript.ScriptFullName)
sh.CurrentDirectory = here
sh.Run """" & here & "\phonon_pro.bat"" hidden", 0, False

@echo off
setlocal
cd /d "%~dp0"
title Phonon Studio Pro

set "HIDDEN=0"
if /i "%~1"=="hidden" set "HIDDEN=1"

set "PY=.venv\Scripts\python.exe"
set "PIPLIST=numpy soundfile pygame safetensors huggingface_hub torch"
set "TFZIP=https://github.com/huggingface/transformers/archive/refs/heads/main.zip"
set "PYTHONUTF8=1"
set "HF_HUB_DISABLE_SYMLINKS_WARNING=1"
set "HF_HUB_DISABLE_TELEMETRY=1"

if "%HIDDEN%"=="1" goto :banner_done
echo ============================================
echo   Phonon Studio Pro
echo ============================================
echo.
:banner_done

if not exist "phonon_studio.py" goto :err_nostudio

rem ---------- stage 1: virtual environment ----------
if exist "%PY%" goto :venv_ok
if "%HIDDEN%"=="1" goto :err_needsetup
echo [*] Creating virtual environment ...
where py >nul 2>nul
if errorlevel 1 goto :err_nopy
py -3.12 -m venv .venv
if errorlevel 1 goto :err_venv
"%PY%" -m pip install --upgrade pip
:venv_ok

rem ---------- stage 2: packages ----------
"%PY%" -c "import numpy, soundfile, pygame, safetensors, huggingface_hub, torch, tokenizers, transformers; from transformers import GradiumPhononTTSForConditionalGeneration" >nul 2>nul
if not errorlevel 1 goto :pkgs_ok
if "%HIDDEN%"=="1" goto :err_needsetup
echo [!] Packages missing. Installing (PyTorch is a big download, be patient) ...
"%PY%" -m pip install %PIPLIST%
if errorlevel 1 goto :err_pip
echo [*] Installing Transformers from GitHub (Phonon is not in the PyPI release yet) ...
"%PY%" -m pip install --upgrade "%TFZIP%"
if errorlevel 1 goto :err_pip
:pkgs_ok

rem ---------- stage 3: model files ----------
if exist "hf_cache\phonon_ready.txt" goto :models_ok
if "%HIDDEN%"=="1" goto :err_needsetup
echo [!] Model files missing. Downloading (a few hundred MB) ...
"%PY%" phonon_studio.py --download
if errorlevel 1 goto :err_download
:models_ok

rem ---------- ffmpeg check ----------
where ffmpeg >nul 2>nul
if not errorlevel 1 goto :ff_path
if exist "ffmpeg.exe" goto :ff_local
echo [!] ffmpeg not found - WAV only.
goto :ff_done
:ff_path
echo [*] ffmpeg found on PATH.
goto :ff_done
:ff_local
echo [*] ffmpeg.exe found locally.
:ff_done

echo.
echo [*] Launching Phonon Studio Pro ...
"%PY%" phonon_studio.py
if errorlevel 1 goto :err_crash
exit /b 0

rem ---------- errors ----------
:err_nostudio
set "MSG=phonon_studio.py is missing next to this .bat file."
goto :fail
:err_needsetup
set "MSG=First-time setup is not finished. Double-click phonon_pro.bat once (the visible one) and let it install and download everything."
goto :fail
:err_nopy
set "MSG=Python launcher py not found. Install Python 3.12 first."
goto :fail
:err_venv
set "MSG=Could not create the virtual environment. Is Python 3.12 installed? Try: py -3.12 --version"
goto :fail
:err_pip
set "MSG=A package install failed. Scroll up for the pip error, fix it, then run this .bat again."
goto :fail
:err_download
set "MSG=The model download failed. Check your internet connection and run this .bat again, it resumes."
goto :fail
:err_crash
set "MSG=The GUI crashed. Run phonon_pro.bat (visible) and scroll up for the details."
goto :fail

:fail
echo.
echo [X] %MSG%
if "%HIDDEN%"=="1" goto :fail_popup
pause
exit /b 1
:fail_popup
> "%TEMP%\phonon_err.vbs" echo MsgBox "%MSG%", 16, "Phonon Studio Pro"
wscript "%TEMP%\phonon_err.vbs"
del "%TEMP%\phonon_err.vbs" >nul 2>nul
exit /b 1

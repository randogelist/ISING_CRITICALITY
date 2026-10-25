@echo off
setlocal EnableExtensions EnableDelayedExpansion
cd /d "%~dp0"

echo RUNNER_ENTERED=PASS
echo PACKAGE=PCD_Q3_8DIGIT_LEAN_v0_1_2_FIX2
echo SCOPE=PCD_Q3_SQUARELOOP_ANALYTIC_8DIGIT_D3_TO_D11
echo MODE=NATIVE_WINDOWS_DIRECT_LEAN_433_CACHED_MATHLIB_ONLY
echo LEAN_NUM_THREADS=16
echo POWERSHELL=NOT_USED
echo PYTHON=NOT_USED
echo WSL=NOT_USED
echo LAKE=NOT_USED
echo NETWORK=NOT_USED
echo DEPENDENCY_DOWNLOAD=DISABLED
echo MATHLIB_BUILD=DISABLED
echo MATHLIB=IMPORTED_FROM_EXISTING_CACHE

echo OLEAN_CLEANUP=LOCAL_OUTPUT_ONLY
set "LEAN_NUM_THREADS=16"
set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not exist "%LEAN_EXE%" (
  echo LEAN_EXE_PRESENT=FAIL
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
echo LEAN_EXE_PRESENT=PASS
echo LEAN_EXE=%LEAN_EXE%
"%LEAN_EXE%" --version
"%LEAN_EXE%" --version | findstr /C:"Lean (version 4.33.0" >nul
if errorlevel 1 (
  echo LEAN_VERSION_CHECK=FAIL
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
echo LEAN_VERSION=4.33.0
echo LEAN_VERSION_CHECK=PASS
"%LEAN_EXE%" --version | findstr /C:"x86_64-w64-windows-gnu" >nul
if errorlevel 1 (
  echo LEAN_TARGET_CHECK=FAIL
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
echo LEAN_TARGET_CHECK=PASS
"%LEAN_EXE%" --version | findstr /C:"d8b18978322de05a8f3dba51ef03cf5461676c17" >nul
if errorlevel 1 (
  echo LEAN_COMMIT_CHECK=FAIL
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
echo LEAN_COMMIT_CHECK=PASS

set "SHARED_WORKSPACE=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
echo SHARED_WORKSPACE=%SHARED_WORKSPACE%
if not exist "%SHARED_WORKSPACE%" (
  echo SHARED_WORKSPACE_PRESENT=FAIL
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
echo SHARED_WORKSPACE_PRESENT=PASS

set "LEAN_PATH=%CD%\_lean_out;%CD%"
set "MATHLIB_LIB="
if exist "%SHARED_WORKSPACE%\.lake\build\lib\lean\Mathlib.olean" set "MATHLIB_LIB=%SHARED_WORKSPACE%\.lake\build\lib\lean"
if exist "%SHARED_WORKSPACE%\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean" set "MATHLIB_LIB=%SHARED_WORKSPACE%\.lake\packages\mathlib\.lake\build\lib\lean"
if not defined MATHLIB_LIB (
  echo MATHLIB_CACHE=NOT_FOUND
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
set "LEAN_PATH=!LEAN_PATH!;!MATHLIB_LIB!"
if exist "%SHARED_WORKSPACE%\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%SHARED_WORKSPACE%\.lake\build\lib\lean"
for /d %%D in ("%SHARED_WORKSPACE%\.lake\packages\*") do (
  if exist "%%~fD\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%%~fD\.lake\build\lib\lean"
)
echo MATHLIB_CACHE=READY_PATH_VERIFIED
echo MATHLIB_LIB=!MATHLIB_LIB!

findstr /S /N /I /C:"sorry" /C:"admit" /C:"axiom " /C:"unsafe " PCD\*.lean Main.lean > "%TEMP%\pcd_q3_escape_scan.txt"
if not errorlevel 1 (
  type "%TEMP%\pcd_q3_escape_scan.txt"
  echo PROOF_ESCAPE_SCAN=FAIL
  echo PROJECT_BUILD=FAIL
  echo RUN=FAIL
  exit /b 1
)
echo PROOF_ESCAPE_SCAN=PASS
echo RESEARCH_AXIOM_DECLARATIONS=0
echo PUBLIC_AXIOM_DECLARATIONS=0

if exist "_lean_out" rmdir /s /q "_lean_out"
mkdir "_lean_out\PCD" >nul 2>&1
echo LOCAL_OUTPUT=%CD%\_lean_out
echo FAST_STARTUP_FOR_LEAN=PASS

call :compile PCD\Q3Defs.lean _lean_out\PCD\Q3Defs.olean COMPILE_Q3_DEFS || goto :fail
call :compile PCD\Q3BaseBounds.lean _lean_out\PCD\Q3BaseBounds.olean COMPILE_Q3_BASE_BOUNDS || goto :fail
call :compile PCD\Q3D3.lean _lean_out\PCD\Q3D3.olean COMPILE_Q3_D3 || goto :fail
call :compile PCD\Q3D4.lean _lean_out\PCD\Q3D4.olean COMPILE_Q3_D4 || goto :fail
call :compile PCD\Q3D5.lean _lean_out\PCD\Q3D5.olean COMPILE_Q3_D5 || goto :fail
call :compile PCD\Q3D6.lean _lean_out\PCD\Q3D6.olean COMPILE_Q3_D6 || goto :fail
call :compile PCD\Q3D7.lean _lean_out\PCD\Q3D7.olean COMPILE_Q3_D7 || goto :fail
call :compile PCD\Q3D8.lean _lean_out\PCD\Q3D8.olean COMPILE_Q3_D8 || goto :fail
call :compile PCD\Q3D9.lean _lean_out\PCD\Q3D9.olean COMPILE_Q3_D9 || goto :fail
call :compile PCD\Q3D10.lean _lean_out\PCD\Q3D10.olean COMPILE_Q3_D10 || goto :fail
call :compile PCD\Q3D11.lean _lean_out\PCD\Q3D11.olean COMPILE_Q3_D11 || goto :fail
call :compile PCD\Q3Aggregate.lean _lean_out\PCD\Q3Aggregate.olean COMPILE_Q3_AGGREGATE || goto :fail

echo COMPILE_MAIN=START
"%LEAN_EXE%" -DwarningAsError=true Main.lean > "_lean_out\Main.audit.txt" 2>&1
if errorlevel 1 (
  type "_lean_out\Main.audit.txt"
  echo FAILED_STAGE=COMPILE_MAIN
  goto :fail
)
type "_lean_out\Main.audit.txt"
findstr /I /C:"sorryAx" "_lean_out\Main.audit.txt" >nul
if not errorlevel 1 (
  echo LEAN_AXIOM_AUDIT=FAIL_SORRYAX
  goto :fail
)
echo COMPILE_MAIN=PASS
echo LEAN_AXIOM_AUDIT=PASS_NO_SORRYAX
echo PROJECT_BUILD=PASS
echo RUN=PASS
exit /b 0

:compile
echo %3=START
"%LEAN_EXE%" -DwarningAsError=true -o "%~2" "%~1"
if errorlevel 1 (
  echo FAILED_STAGE=%3
  exit /b 1
)
echo %3=PASS
exit /b 0

:fail
echo PROJECT_BUILD=FAIL
echo RUN=FAIL
exit /b 1

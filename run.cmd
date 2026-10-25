@echo off
setlocal
cd /d "%~dp0"
where g++ >nul 2>nul
if errorlevel 1 (echo ERROR: Install GCC/MinGW C++17 and put g++ on PATH.& exit /b 1)
if not exist build mkdir build
g++ -std=c++17 -O2 -Wall -Wextra numerics\pcd.cpp -o build\pcd.exe
if errorlevel 1 exit /b 1
build\pcd.exe --self-test
if errorlevel 1 exit /b 1
py -3 -m unittest discover -s literature -p "test_*.py"
if errorlevel 1 exit /b 1
py -3 scripts\make_tables.py --exe build\pcd.exe
if errorlevel 1 exit /b 1
echo NUMERICS=PASS
echo LEAN=CI_ONLY; push the source or dispatch the Verify Lean and C++ GitHub Actions workflow.

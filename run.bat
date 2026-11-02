@echo off
setlocal
cd /d "%~dp0"
"%~dp0python-3.14.10-embed-amd64\python.exe" "%~dp0FRM-PNG-WIN.py"
if errorlevel 1 pause
endlocal

#!/usr/bin/env python3
"""
Compile and simulate the ALU testbench
Author: Verification Team
Date: February 2026
"""

import os
import sys
import argparse
import subprocess
from pathlib import Path

def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description='Compile and simulate ALU testbench',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    
    parser.add_argument('--simulator', '-s', 
                       choices=['questa', 'vcs', 'xcelium'],
                       default='questa',
                       help='Simulator to use')
    
    parser.add_argument('--test', '-t',
                       choices=['directed', 'random', 'corner', 'all'],
                       default='random',
                       help='Test type to run')
    
    parser.add_argument('--width', '-w',
                       type=int,
                       default=32,
                       choices=[8, 16, 32, 64],
                       help='ALU data width')
    
    parser.add_argument('--seed', '-sd',
                       type=int,
                       default=None,
                       help='Random seed (auto-generated if not specified)')
    
    parser.add_argument('--ntests', '-n',
                       type=int,
                       default=1000,
                       help='Number of random tests')
    
    parser.add_argument('--gui', '-g',
                       action='store_true',
                       help='Open simulator GUI')
    
    parser.add_argument('--coverage', '-c',
                       action='store_true',
                       help='Enable coverage collection')
    
    parser.add_argument('--waves', '-v',
                       action='store_true',
                       help='Dump waveforms')
    
    parser.add_argument('--clean',
                       action='store_true',
                       help='Clean before compile')
    
    return parser.parse_args()

def get_file_lists():
    """Get lists of RTL and verification files"""
    rtl_files = [
        'rtl/alu_pkg.sv',
        'rtl/param_alu.sv'
    ]
    
    verif_files = [
        'verif/alu_tb_pkg.sv',
        'verif/alu_driver.sv',
        'verif/alu_monitor.sv',
        'verif/alu_scoreboard.sv',
        'verif/alu_coverage.sv',
        'verif/alu_assertions.sv',
        'verif/alu_tb_top.sv'
    ]
    
    test_files = [
        'tests/alu_directed_test.sv',
        'tests/alu_random_test.sv'
    ]
    
    return rtl_files + verif_files + test_files

def clean_work_directory():
    """Clean simulation work directory"""
    print("Cleaning work directory...")
    
    dirs_to_clean = ['work', 'transcript', 'vsim.wlf', 'modelsim.ini', 
                     'coverage.ucdb', '*.log', '*.vcd']
    
    for pattern in dirs_to_clean:
        os.system(f'rm -rf {pattern}')
    
    print("Clean complete.\n")

def compile_questa(files, width, coverage):
    """Compile using QuestaSim"""
    print("=== Compiling with QuestaSim ===\n")
    
    # Create work library
    cmd = 'vlib work'
    print(f"$ {cmd}")
    result = subprocess.run(cmd, shell=True)
    if result.returncode != 0:
        print("ERROR: Failed to create work library")
        return False
    
    # Compile files
    coverage_opt = '+cover=sbceft' if coverage else ''
    defines = f'+define+WIDTH={width}'
    
    cmd = f'vlog -sv {coverage_opt} {defines} -work work ' + ' '.join(files)
    print(f"$ {cmd}\n")
    
    result = subprocess.run(cmd, shell=True)
    if result.returncode != 0:
        print("ERROR: Compilation failed")
        return False
    
    print("\n=== Compilation successful ===\n")
    return True

def simulate_questa(test, width, seed, ntests, gui, coverage, waves):
    """Simulate using QuestaSim"""
    print("=== Running Simulation ===\n")
    
    # Generate seed if not provided
    if seed is None:
        import random
        seed = random.randint(1, 999999)
    
    # Build simulation command
    plusargs = f'+TEST={test} +NTESTS={ntests} +SEED={seed}'
    
    if gui:
        cmd = f'vsim -gui -coverage alu_tb_top {plusargs}'
        if waves:
            cmd += ' -do "log -r /*; run -all"'
    else:
        coverage_opt = '-coverage' if coverage else ''
        wave_opt = '-do "log -r /*; run -all; quit"' if waves else '-do "run -all; quit"'
        cmd = f'vsim -c {coverage_opt} alu_tb_top {plusargs} {wave_opt}'
    
    print(f"$ {cmd}\n")
    print(f"Test configuration:")
    print(f"  Test type: {test}")
    print(f"  WIDTH: {width}")
    print(f"  Seed: {seed}")
    print(f"  Number of tests: {ntests}")
    print("")
    
    result = subprocess.run(cmd, shell=True)
    
    if result.returncode != 0:
        print("\nERROR: Simulation failed")
        return False
    
    print("\n=== Simulation complete ===\n")
    return True

def generate_coverage_report():
    """Generate coverage report"""
    print("=== Generating Coverage Report ===\n")
    
    # Text report
    cmd = 'vcover report -details -file coverage_report.txt coverage.ucdb'
    print(f"$ {cmd}")
    subprocess.run(cmd, shell=True)
    
    # HTML report
    cmd = 'vcover report -html -htmldir coverage_html -verbose coverage.ucdb'
    print(f"$ {cmd}\n")
    subprocess.run(cmd, shell=True)
    
    print("Coverage report generated:")
    print("  Text: coverage_report.txt")
    print("  HTML: coverage_html/index.html\n")

def main():
    """Main function"""
    args = parse_arguments()
    
    print("="*70)
    print("ALU Testbench Compilation and Simulation")
    print("="*70)
    print("")
    
    # Clean if requested
    if args.clean:
        clean_work_directory()
    
    # Get file lists
    files = get_file_lists()
    
    # Check if files exist
    missing_files = [f for f in files if not os.path.exists(f)]
    if missing_files:
        print("ERROR: Missing files:")
        for f in missing_files:
            print(f"  - {f}")
        return 1
    
    # Compile
    if args.simulator == 'questa':
        if not compile_questa(files, args.width, args.coverage):
            return 1
    else:
        print(f"ERROR: Simulator {args.simulator} not yet supported")
        return 1
    
    # Simulate
    if args.simulator == 'questa':
        if not simulate_questa(args.test, args.width, args.seed, 
                               args.ntests, args.gui, args.coverage, args.waves):
            return 1
    
    # Generate coverage report if enabled
    if args.coverage and not args.gui:
        generate_coverage_report()
    
    print("="*70)
    print("SUCCESS")
    print("="*70)
    
    return 0

if __name__ == '__main__':
    sys.exit(main())

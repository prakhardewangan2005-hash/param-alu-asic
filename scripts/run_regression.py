#!/usr/bin/env python3
"""
Run regression testing for ALU testbench
Author: Verification Team
Date: February 2026
"""

import os
import sys
import argparse
import subprocess
import json
from datetime import datetime
from pathlib import Path

def parse_arguments():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description='Run ALU regression tests',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    
    parser.add_argument('--tests', '-t',
                       nargs='+',
                       default=['all'],
                       help='Tests to run (directed, random, corner, all)')
    
    parser.add_argument('--widths', '-w',
                       type=str,
                       default='8,16,32,64',
                       help='Comma-separated list of widths to test')
    
    parser.add_argument('--seeds', '-s',
                       type=int,
                       default=10,
                       help='Number of random seeds for random tests')
    
    parser.add_argument('--ntests', '-n',
                       type=int,
                       default=1000,
                       help='Number of tests per seed')
    
    parser.add_argument('--parallel', '-p',
                       type=int,
                       default=1,
                       help='Number of parallel jobs')
    
    parser.add_argument('--coverage',
                       action='store_true',
                       help='Enable coverage collection')
    
    parser.add_argument('--output', '-o',
                       default='regression_results',
                       help='Output directory for results')
    
    return parser.parse_args()

class RegressionRunner:
    """Class to manage regression testing"""
    
    def __init__(self, args):
        self.args = args
        self.results = []
        self.start_time = datetime.now()
        
        # Parse widths
        self.widths = [int(w) for w in args.widths.split(',')]
        
        # Create output directory
        self.output_dir = Path(args.output)
        self.output_dir.mkdir(exist_ok=True)
        
    def run_single_test(self, test_type, width, seed=None):
        """Run a single test configuration"""
        test_name = f"{test_type}_w{width}"
        if seed is not None:
            test_name += f"_s{seed}"
        
        print(f"\n{'='*70}")
        print(f"Running: {test_name}")
        print(f"{'='*70}")
        
        # Build command
        cmd = f"python3 scripts/compile_sim.py -t {test_type} -w {width}"
        
        if seed is not None:
            cmd += f" -sd {seed}"
        
        cmd += f" -n {self.args.ntests}"
        
        if self.args.coverage:
            cmd += " -c"
        
        # Redirect output
        log_file = self.output_dir / f"{test_name}.log"
        cmd += f" > {log_file} 2>&1"
        
        # Run test
        start = datetime.now()
        result = subprocess.run(cmd, shell=True)
        duration = (datetime.now() - start).total_seconds()
        
        # Parse results
        passed = result.returncode == 0
        
        # Store result
        test_result = {
            'test_name': test_name,
            'test_type': test_type,
            'width': width,
            'seed': seed,
            'passed': passed,
            'duration': duration,
            'log_file': str(log_file)
        }
        
        self.results.append(test_result)
        
        # Print result
        status = "PASSED" if passed else "FAILED"
        print(f"\nResult: {status} (Duration: {duration:.2f}s)")
        
        return passed
    
    def run_directed_tests(self):
        """Run all directed tests"""
        print("\n" + "="*70)
        print("DIRECTED TESTS")
        print("="*70)
        
        all_passed = True
        for width in self.widths:
            passed = self.run_single_test('directed', width)
            all_passed = all_passed and passed
        
        return all_passed
    
    def run_corner_tests(self):
        """Run all corner case tests"""
        print("\n" + "="*70)
        print("CORNER CASE TESTS")
        print("="*70)
        
        all_passed = True
        for width in self.widths:
            passed = self.run_single_test('corner', width)
            all_passed = all_passed and passed
        
        return all_passed
    
    def run_random_tests(self):
        """Run random tests with multiple seeds"""
        print("\n" + "="*70)
        print("RANDOM TESTS")
        print("="*70)
        
        all_passed = True
        for width in self.widths:
            for seed_idx in range(self.args.seeds):
                seed = seed_idx + 1000
                passed = self.run_single_test('random', width, seed)
                all_passed = all_passed and passed
        
        return all_passed
    
    def generate_report(self):
        """Generate regression report"""
        print("\n" + "="*70)
        print("REGRESSION SUMMARY")
        print("="*70)
        
        total_tests = len(self.results)
        passed_tests = sum(1 for r in self.results if r['passed'])
        failed_tests = total_tests - passed_tests
        
        total_duration = sum(r['duration'] for r in self.results)
        
        print(f"\nTotal tests run: {total_tests}")
        print(f"Passed: {passed_tests}")
        print(f"Failed: {failed_tests}")
        print(f"Pass rate: {100.0 * passed_tests / total_tests:.1f}%")
        print(f"Total duration: {total_duration:.2f}s")
        print(f"Average duration: {total_duration / total_tests:.2f}s")
        
        # Print failed tests
        if failed_tests > 0:
            print("\nFailed tests:")
            for r in self.results:
                if not r['passed']:
                    print(f"  - {r['test_name']}")
                    print(f"    Log: {r['log_file']}")
        
        # Save JSON report
        report_file = self.output_dir / 'regression_report.json'
        report_data = {
            'start_time': self.start_time.isoformat(),
            'end_time': datetime.now().isoformat(),
            'total_tests': total_tests,
            'passed': passed_tests,
            'failed': failed_tests,
            'pass_rate': 100.0 * passed_tests / total_tests,
            'total_duration': total_duration,
            'results': self.results
        }
        
        with open(report_file, 'w') as f:
            json.dump(report_data, f, indent=2)
        
        print(f"\nDetailed report saved to: {report_file}")
        
        # Generate HTML report
        self.generate_html_report(report_data)
        
        return failed_tests == 0
    
    def generate_html_report(self, report_data):
        """Generate HTML report"""
        html_file = self.output_dir / 'regression_report.html'
        
        html = f"""
<!DOCTYPE html>
<html>
<head>
    <title>ALU Regression Report</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        h1 {{ color: #333; }}
        table {{ border-collapse: collapse; width: 100%; margin-top: 20px; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #4CAF50; color: white; }}
        tr:nth-child(even) {{ background-color: #f2f2f2; }}
        .passed {{ color: green; font-weight: bold; }}
        .failed {{ color: red; font-weight: bold; }}
        .summary {{ background-color: #f0f0f0; padding: 15px; border-radius: 5px; margin: 20px 0; }}
    </style>
</head>
<body>
    <h1>ALU Regression Test Report</h1>
    
    <div class="summary">
        <h2>Summary</h2>
        <p><strong>Start Time:</strong> {report_data['start_time']}</p>
        <p><strong>End Time:</strong> {report_data['end_time']}</p>
        <p><strong>Total Tests:</strong> {report_data['total_tests']}</p>
        <p><strong>Passed:</strong> {report_data['passed']}</p>
        <p><strong>Failed:</strong> {report_data['failed']}</p>
        <p><strong>Pass Rate:</strong> {report_data['pass_rate']:.1f}%</p>
        <p><strong>Total Duration:</strong> {report_data['total_duration']:.2f}s</p>
    </div>
    
    <h2>Detailed Results</h2>
    <table>
        <tr>
            <th>Test Name</th>
            <th>Type</th>
            <th>Width</th>
            <th>Seed</th>
            <th>Status</th>
            <th>Duration (s)</th>
            <th>Log File</th>
        </tr>
"""
        
        for r in report_data['results']:
            status_class = 'passed' if r['passed'] else 'failed'
            status_text = 'PASSED' if r['passed'] else 'FAILED'
            seed_text = str(r['seed']) if r['seed'] is not None else 'N/A'
            
            html += f"""
        <tr>
            <td>{r['test_name']}</td>
            <td>{r['test_type']}</td>
            <td>{r['width']}</td>
            <td>{seed_text}</td>
            <td class="{status_class}">{status_text}</td>
            <td>{r['duration']:.2f}</td>
            <td><a href="{r['log_file']}">{Path(r['log_file']).name}</a></td>
        </tr>
"""
        
        html += """
    </table>
</body>
</html>
"""
        
        with open(html_file, 'w') as f:
            f.write(html)
        
        print(f"HTML report saved to: {html_file}")
    
    def run(self):
        """Run regression tests"""
        tests_to_run = self.args.tests
        
        if 'all' in tests_to_run:
            tests_to_run = ['directed', 'corner', 'random']
        
        all_passed = True
        
        if 'directed' in tests_to_run:
            all_passed = self.run_directed_tests() and all_passed
        
        if 'corner' in tests_to_run:
            all_passed = self.run_corner_tests() and all_passed
        
        if 'random' in tests_to_run:
            all_passed = self.run_random_tests() and all_passed
        
        # Generate report
        success = self.generate_report()
        
        return 0 if success else 1

def main():
    """Main function"""
    args = parse_arguments()
    
    runner = RegressionRunner(args)
    return runner.run()

if __name__ == '__main__':
    sys.exit(main())

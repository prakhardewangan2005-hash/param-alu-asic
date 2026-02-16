#!/usr/bin/env python3
"""
Summarize test results and generate reports
Author: Verification Team
Date: February 2026
"""

import os
import sys
import json
import re
from pathlib import Path
from datetime import datetime

def parse_log_file(log_file):
    """Parse a simulation log file for key metrics"""
    results = {
        'transactions_checked': 0,
        'transactions_passed': 0,
        'transactions_failed': 0,
        'coverage': 0.0,
        'errors': [],
        'warnings': []
    }
    
    if not os.path.exists(log_file):
        return results
    
    with open(log_file, 'r') as f:
        content = f.read()
    
    # Extract transaction counts
    match = re.search(r'Total transactions checked:\s*(\d+)', content)
    if match:
        results['transactions_checked'] = int(match.group(1))
    
    match = re.search(r'Transactions passed:\s*(\d+)', content)
    if match:
        results['transactions_passed'] = int(match.group(1))
    
    match = re.search(r'Transactions failed:\s*(\d+)', content)
    if match:
        results['transactions_failed'] = int(match.group(1))
    
    # Extract coverage
    match = re.search(r'Weighted Total Coverage:\s*([\d.]+)%', content)
    if match:
        results['coverage'] = float(match.group(1))
    
    # Extract errors
    for match in re.finditer(r'ERROR:(.+?)$', content, re.MULTILINE):
        results['errors'].append(match.group(1).strip())
    
    # Extract warnings
    for match in re.finditer(r'WARNING:(.+?)$', content, re.MULTILINE):
        results['warnings'].append(match.group(1).strip())
    
    return results

def summarize_regression(results_dir='regression_results'):
    """Summarize regression test results"""
    results_path = Path(results_dir)
    
    if not results_path.exists():
        print(f"ERROR: Results directory '{results_dir}' not found")
        return
    
    # Load JSON report if it exists
    json_report = results_path / 'regression_report.json'
    if json_report.exists():
        with open(json_report, 'r') as f:
            report_data = json.load(f)
    else:
        print(f"ERROR: Regression report '{json_report}' not found")
        return
    
    # Print summary
    print("="*70)
    print("REGRESSION TEST SUMMARY")
    print("="*70)
    print()
    
    print(f"Report generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Start time: {report_data['start_time']}")
    print(f"End time: {report_data['end_time']}")
    print()
    
    print("OVERALL RESULTS:")
    print(f"  Total tests: {report_data['total_tests']}")
    print(f"  Passed: {report_data['passed']}")
    print(f"  Failed: {report_data['failed']}")
    print(f"  Pass rate: {report_data['pass_rate']:.1f}%")
    print(f"  Total duration: {report_data['total_duration']:.2f}s")
    print()
    
    # Analyze by test type
    test_types = {}
    for result in report_data['results']:
        test_type = result['test_type']
        if test_type not in test_types:
            test_types[test_type] = {'total': 0, 'passed': 0, 'failed': 0}
        
        test_types[test_type]['total'] += 1
        if result['passed']:
            test_types[test_type]['passed'] += 1
        else:
            test_types[test_type]['failed'] += 1
    
    print("RESULTS BY TEST TYPE:")
    for test_type, stats in test_types.items():
        pass_rate = 100.0 * stats['passed'] / stats['total']
        print(f"  {test_type}:")
        print(f"    Total: {stats['total']}")
        print(f"    Passed: {stats['passed']}")
        print(f"    Failed: {stats['failed']}")
        print(f"    Pass rate: {pass_rate:.1f}%")
    print()
    
    # Analyze by width
    widths = {}
    for result in report_data['results']:
        width = result['width']
        if width not in widths:
            widths[width] = {'total': 0, 'passed': 0, 'failed': 0}
        
        widths[width]['total'] += 1
        if result['passed']:
            widths[width]['passed'] += 1
        else:
            widths[width]['failed'] += 1
    
    print("RESULTS BY WIDTH:")
    for width in sorted(widths.keys()):
        stats = widths[width]
        pass_rate = 100.0 * stats['passed'] / stats['total']
        print(f"  WIDTH={width}:")
        print(f"    Total: {stats['total']}")
        print(f"    Passed: {stats['passed']}")
        print(f"    Failed: {stats['failed']}")
        print(f"    Pass rate: {pass_rate:.1f}%")
    print()
    
    # List failed tests
    failed_tests = [r for r in report_data['results'] if not r['passed']]
    if failed_tests:
        print("FAILED TESTS:")
        for test in failed_tests:
            print(f"  - {test['test_name']}")
            print(f"    Duration: {test['duration']:.2f}s")
            print(f"    Log: {test['log_file']}")
        print()
    
    # Parse detailed metrics from log files
    print("DETAILED METRICS (from log files):")
    total_transactions = 0
    total_coverage_sum = 0.0
    coverage_count = 0
    
    for result in report_data['results']:
        log_file = result['log_file']
        metrics = parse_log_file(log_file)
        
        total_transactions += metrics['transactions_checked']
        
        if metrics['coverage'] > 0:
            total_coverage_sum += metrics['coverage']
            coverage_count += 1
    
    if coverage_count > 0:
        avg_coverage = total_coverage_sum / coverage_count
        print(f"  Total transactions checked: {total_transactions}")
        print(f"  Average coverage: {avg_coverage:.2f}%")
    
    print()
    print("="*70)
    
    # Final verdict
    if report_data['failed'] == 0:
        print("VERDICT: ALL TESTS PASSED ✓")
    else:
        print(f"VERDICT: {report_data['failed']} TESTS FAILED ✗")
    
    print("="*70)

def main():
    """Main function"""
    if len(sys.argv) > 1:
        results_dir = sys.argv[1]
    else:
        results_dir = 'regression_results'
    
    summarize_regression(results_dir)

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""
Single script to convert JSON trace files or TLA+ model checker output to dbdiag format.
This script combines extraction and conversion in one step, outputting to transaction_history.txt

By default, it processes JSON trace files from the traces/ directory.

Usage:
    python tla_to_transaction_history.py [input_file]
"""

import sys
import re
import json
import os
import glob
from typing import List, Dict, Any
from dataclasses import dataclass

@dataclass
class Transaction:
    id: str
    start_time: int
    end_time: int
    events: List[tuple]  # (time, operation, key)

def parse_tla_history_entry(history_str: str) -> List[Dict[str, Any]]:
    """
    Parse a single TLA+ history entry string into a list of operations.
    
    Args:
        history_str: TLA+ format history string like "<<[type |-> "begin", ...]>>"
    
    Returns:
        List of operation dictionaries
    """
    # Remove the outer << >> brackets
    history_str = history_str.strip()
    if history_str.startswith('<<') and history_str.endswith('>>'):
        history_str = history_str[2:-2].strip()
    
    if not history_str:
        return []
    
    operations = []
    
    # Split by '], [' to separate individual operations
    # But be careful with nested structures
    current_op = ""
    bracket_count = 0
    in_string = False
    
    i = 0
    while i < len(history_str):
        char = history_str[i]
        
        if char == '"' and (i == 0 or history_str[i-1] != '\\'):
            in_string = not in_string
        elif not in_string:
            if char == '[':
                bracket_count += 1
            elif char == ']':
                bracket_count -= 1
                
        current_op += char
        
        # If we've completed an operation (bracket_count == 0 and we just closed a bracket)
        if not in_string and bracket_count == 0 and char == ']':
            # Check if the next characters are ', [' (indicating another operation)
            if i + 1 < len(history_str) and history_str[i+1:i+3] == ', ':
                # Parse the current operation
                op = parse_single_operation(current_op.strip())
                if op:
                    operations.append(op)
                current_op = ""
                i += 2  # Skip the ', '
            elif i == len(history_str) - 1:
                # Last operation
                op = parse_single_operation(current_op.strip())
                if op:
                    operations.append(op)
        
        i += 1
    
    # Handle case where there's only one operation
    if bracket_count == 0 and current_op.strip():
        op = parse_single_operation(current_op.strip())
        if op:
            operations.append(op)
    
    return operations

def parse_single_operation(op_str: str) -> Dict[str, Any]:
    """
    Parse a single TLA+ operation string.
    
    Args:
        op_str: Single operation like '[type |-> "begin", txnId |-> t0, time |-> 1]'
    
    Returns:
        Dictionary with operation details
    """
    op_str = op_str.strip()
    if not op_str.startswith('[') or not op_str.endswith(']'):
        return {}
    
    # Remove brackets
    op_str = op_str[1:-1]
    
    # Parse key-value pairs
    op_dict = {}
    
    # Split by ', ' but be careful with nested structures
    pairs = []
    current_pair = ""
    in_string = False
    brace_count = 0
    
    for char in op_str:
        if char == '"' and (not current_pair or current_pair[-1] != '\\'):
            in_string = not in_string
        elif not in_string:
            if char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
        
        if not in_string and brace_count == 0 and char == ',' and current_pair.strip():
            pairs.append(current_pair.strip())
            current_pair = ""
        else:
            current_pair += char
    
    if current_pair.strip():
        pairs.append(current_pair.strip())
    
    # Parse each key-value pair
    for pair in pairs:
        if ' |-> ' in pair:
            key, value = pair.split(' |-> ', 1)
            key = key.strip()
            value = value.strip()
            
            # Remove quotes if present
            if value.startswith('"') and value.endswith('"'):
                value = value[1:-1]
            elif value.startswith('{') and value.endswith('}'):
                # Handle sets like {k2, k4, k6}
                set_content = value[1:-1].strip()
                if set_content:
                    value = [item.strip() for item in set_content.split(',')]
                else:
                    value = []
            elif value.isdigit():
                value = int(value)
            
            op_dict[key] = value
    
    return op_dict

def extract_ccgraph_transactions(input_file: str) -> set:
    """
    Extract the set of transaction IDs that are part of the final ccgraph.
    
    Args:
        input_file: Path to the JSON trace file
        
    Returns:
        Set of transaction IDs in the final ccgraph, or None if not found
    """
    try:
        with open(input_file, 'r') as f:
            content = f.read()
        
        # Only process JSON files for ccgraph extraction
        if not input_file.endswith('.json'):
            return None
        
        try:
            data = json.loads(content)
            # Extract ccgraph from the final state in the trace
            if 'state' in data:
                states = data['state']
                # Look backwards for the last state with a non-empty ccgraph
                for i in range(len(states) - 1, -1, -1):
                    if len(states[i]) >= 2 and isinstance(states[i][1], dict):
                        state_data = states[i][1]
                        if 'ccgraph' in state_data and state_data['ccgraph']:
                            ccgraph = state_data['ccgraph']
                            # Extract unique transaction IDs from ccgraph edges
                            txn_ids = set()
                            for edge in ccgraph:
                                if len(edge) >= 2:
                                    # Convert t1 -> T1, t2 -> T2, etc.
                                    txn1 = edge[0]
                                    txn2 = edge[1]
                                    if txn1.startswith('t') and txn1[1:].isdigit():
                                        txn1 = 'T' + txn1[1:]
                                    if txn2.startswith('t') and txn2[1:].isdigit():
                                        txn2 = 'T' + txn2[1:]
                                    txn_ids.add(txn1)
                                    txn_ids.add(txn2)
                            return txn_ids
            return None
        except json.JSONDecodeError:
            return None
        
    except FileNotFoundError:
        print(f"Error: Input file '{input_file}' not found.")
        return None
    except Exception as e:
        print(f"Error processing file: {e}")
        return None

def extract_final_txnhistory(input_file: str) -> str:
    """
    Extract the final transaction history from TLA+ model checker output.
    
    Args:
        input_file: Path to the TLA+ model checker output file
        
    Returns:
        Final transaction history string or None if not found
    """
    try:
        with open(input_file, 'r') as f:
            content = f.read()
        
        # Check if this is a JSON file
        if input_file.endswith('.json'):
            try:
                data = json.loads(content)
                # Extract txnHistory from each state in the trace
                if 'state' in data:
                    states = data['state']
                    for i in range(len(states) - 1, -1, -1):  # Search backwards for last non-empty
                        if len(states[i]) >= 2 and isinstance(states[i][1], dict):
                            state_data = states[i][1]
                            if 'txnHistory' in state_data and state_data['txnHistory']:
                                return json.dumps(state_data['txnHistory'])
                return None
            except json.JSONDecodeError:
                pass
        
        # Handle TLA+ text output
        lines = content.split('\n')
        final_history = None
        
        # Look for the last step with non-empty transaction history
        last_step_num = 0
        for i, line in enumerate(lines):
            if re.match(r'^\d+:', line):
                step_num = i + 1
                # Look for txnHistory in the next few lines
                for j in range(i+1, min(i+10, len(lines))):
                    if '/\\ txnHistory =' in lines[j]:
                        # Get the full history (might span multiple lines)
                        history_start = j
                        history_lines = []
                        for k in range(history_start, len(lines)):
                            history_lines.append(lines[k])
                            if lines[k].strip().endswith('>>') and k > history_start:
                                break
                        
                        history_str = ' '.join(history_lines)
                        # Extract just the history part
                        if '/\\ txnHistory =' in history_str:
                            history_content = history_str.split('/\\ txnHistory =', 1)[1].strip()
                            # Skip empty histories
                            if history_content != '<<>>':
                                if step_num > last_step_num:
                                    last_step_num = step_num
                                    final_history = history_content
                        break
        
        return final_history
        
    except FileNotFoundError:
        print(f"Error: Input file '{input_file}' not found.")
        return None
    except Exception as e:
        print(f"Error processing file: {e}")
        return None

def convert_to_dbdiag(final_history: str, is_json: bool = False, ccgraph_txns: set = None) -> List[str]:
    """
    Convert transaction history to dbdiag format.
    
    Args:
        final_history: Transaction history string
        is_json: Whether the input is JSON format
        ccgraph_txns: Set of transaction IDs from ccgraph to filter by (optional)
        
    Returns:
        List of dbdiag format lines
    """
    if is_json:
        try:
            operations = json.loads(final_history)
        except json.JSONDecodeError:
            print("Error parsing JSON transaction history.")
            return []
    else:
        operations = parse_tla_history_entry(final_history)
    
    if not operations:
        print("No operations found in the transaction history.")
        return []
    
    # Convert to dbdiag format
    dbdiag_lines = []
    seen_lines = set()  # To avoid duplicates
    
    for op in operations:
        txn_id_raw = op.get('txnId', 'UNKNOWN')
        # Convert to uppercase T format (t0 -> T0, t1 -> T1, etc.)
        if txn_id_raw.startswith('t') and txn_id_raw[1:].isdigit():
            txn_id = 'T' + txn_id_raw[1:]
        else:
            txn_id = txn_id_raw.upper()
        
        # Filter by ccgraph transactions if specified
        if ccgraph_txns is not None and txn_id not in ccgraph_txns:
            continue
        
        op_type = op.get('type', 'unknown')
        
        line = None
        if op_type == 'begin':
            line = f"{txn_id}: BEGIN {txn_id}"
        elif op_type == 'read':
            key = op.get('key', 'unknown_key')
            line = f"{txn_id}: EVENT R({key})"
        elif op_type == 'write':
            key = op.get('key', 'unknown_key')
            line = f"{txn_id}: EVENT W({key})"
        elif op_type == 'commit':
            line = f"{txn_id}: END {txn_id}"
        
        # Add line if it's not a duplicate
        if line and line not in seen_lines:
            dbdiag_lines.append(line)
            seen_lines.add(line)
    
    return dbdiag_lines

def parse_transaction_history(content: str) -> List[Transaction]:
    """Parse transaction_history.txt format into transaction objects."""
    lines = [line.strip() for line in content.split('\n') if line.strip()]
    
    transactions = {}
    time_counter = 0
    
    for line in lines:
        # Parse line format: "T1: BEGIN T1" or "T1: EVENT R(k1)" or "T1: END T1"
        match = re.match(r'(\w+):\s+(BEGIN|EVENT|END)\s+(.+)', line)
        if not match:
            continue
            
        txn_id = match.group(1)
        operation_type = match.group(2)
        operation_detail = match.group(3)
        
        if txn_id not in transactions:
            transactions[txn_id] = {
                'id': txn_id,
                'start_time': None,
                'end_time': None,
                'events': []
            }
        
        if operation_type == 'BEGIN':
            transactions[txn_id]['start_time'] = time_counter
        elif operation_type == 'EVENT':
            # Parse EVENT R(k1) or EVENT W(k2)
            event_match = re.match(r'([RW])\((.+)\)', operation_detail)
            if event_match:
                op = event_match.group(1)
                key = event_match.group(2)
                transactions[txn_id]['events'].append((time_counter, op, key))
        elif operation_type == 'END':
            transactions[txn_id]['end_time'] = time_counter
            
        time_counter += 1
    
    # Convert to Transaction objects
    result = []
    for txn_data in transactions.values():
        if txn_data['start_time'] is not None:
            end_time = txn_data['end_time'] if txn_data['end_time'] is not None else time_counter
            result.append(Transaction(
                id=txn_data['id'],
                start_time=txn_data['start_time'],
                end_time=end_time,
                events=txn_data['events']
            ))
    
    return sorted(result, key=lambda t: t.start_time)

def create_svg_visualization(transactions: List[Transaction], title: str = "Transaction History") -> str:
    """Create SVG visualization of transactions."""
    
    if not transactions:
        return "<svg><text>No transactions found</text></svg>"
    
    # Calculate dimensions
    max_time = max(t.end_time for t in transactions) if transactions else 0
    num_transactions = len(transactions)
    
    # SVG settings
    margin_left = 80
    margin_top = 80
    margin_right = 80
    margin_bottom = 50
    x_scale = 70  # Increased spacing between time units
    y_scale = 80  # Increased spacing between transactions
    
    width = margin_left + margin_right + (max_time + 1) * x_scale
    height = margin_top + margin_bottom + num_transactions * y_scale
    
    svg_parts = [
        f'<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">',
        f'<rect width="{width}" height="{height}" fill="white"/>',
        f'<text x="10" y="20" font-family="monospace" font-size="14">{title}</text>'
    ]
    
    # Draw transactions in reverse order (to match the image layout)
    for i, txn in enumerate(reversed(transactions)):
        y = margin_top + i * y_scale
        
        # Get start and end positions based on time
        x_start = margin_left + txn.start_time * x_scale
        x_end = margin_left + txn.end_time * x_scale
        
        # Draw transaction timeline
        svg_parts.append(f'<line x1="{x_start}" y1="{y}" x2="{x_end}" y2="{y}" stroke="black" stroke-width="2"/>')
        
        # Draw start and end markers (vertical lines)
        svg_parts.append(f'<line x1="{x_start}" y1="{y-15}" x2="{x_start}" y2="{y+15}" stroke="black" stroke-width="2"/>')
        svg_parts.append(f'<line x1="{x_end}" y1="{y-15}" x2="{x_end}" y2="{y+15}" stroke="black" stroke-width="2"/>')
        
        # Transaction label on the left
        svg_parts.append(f'<text x="{x_start-50}" y="{y+5}" font-family="Arial, sans-serif" font-size="16" font-weight="bold">{txn.id}</text>')
        
        # Draw events as red dots
        for event_time, op, key in txn.events:
            event_x = margin_left + event_time * x_scale
            # Red circle for event
            svg_parts.append(f'<circle cx="{event_x}" cy="{y}" r="6" fill="red"/>')
            # Event label above
            svg_parts.append(f'<text x="{event_x-20}" y="{y-20}" font-family="Arial, sans-serif" font-size="14" fill="red">{op}({key})</text>')
    
    svg_parts.append('</svg>')
    return '\n'.join(svg_parts)


def process_single_file(input_file: str, output_base: str) -> bool:
    """Process a single trace file and generate outputs.
    
    Args:
        input_file: Path to the input file
        output_base: Base name for output files (without extension)
        
    Returns:
        True if successful, False otherwise
    """
    output_file = f"{output_base}.txt"
    svg_file = f"{output_base}.svg"
    png_file = f"{output_base}.png"
    
    print(f"Converting {input_file} to dbdiag format -> {output_file}")
    
    # Extract ccgraph transactions (only for JSON files)
    ccgraph_txns = None
    if input_file.endswith('.json'):
        ccgraph_txns = extract_ccgraph_transactions(input_file)
        if ccgraph_txns:
            print(f"Found ccgraph with transactions: {sorted(ccgraph_txns)}")
            print(f"Filtering to only include transactions in the conflict graph")
        else:
            print("No ccgraph found - including all transactions")
    
    # Extract final transaction history
    final_history = extract_final_txnhistory(input_file)
    
    if not final_history:
        print("No transaction history found in the input file.")
        return False
    
    # Convert to dbdiag format
    is_json = input_file.endswith('.json')
    dbdiag_lines = convert_to_dbdiag(final_history, is_json, ccgraph_txns)
    
    if not dbdiag_lines:
        print("Failed to convert transaction history to dbdiag format.")
        return False
    
    # Write output
    try:
        # Ensure directory exists
        output_dir = os.path.dirname(output_file)
        if output_dir:
            os.makedirs(output_dir, exist_ok=True)
        
        with open(output_file, 'w') as f:
            for line in dbdiag_lines:
                f.write(line + '\n')
        
        print(f"Conversion completed successfully!")
        print(f"dbdiag format output written to: {output_file}")
        print(f"Generated {len(dbdiag_lines)} transaction operations")
        
        # Generate visualization
        try:
            # Read transaction history
            with open(output_file, 'r') as f:
                content = f.read()
            
            print("\nGenerating visualization...")
            transactions = parse_transaction_history(content)
            
            if not transactions:
                print("No transactions found for visualization")
                return True  # Still consider it successful if conversion worked
            
            print(f"Found {len(transactions)} transactions")
            
            # Create visualization
            svg_content = create_svg_visualization(transactions, "Transaction History Visualization")
            
            # Ensure directories exist
            svg_dir = os.path.dirname(svg_file)
            png_dir = os.path.dirname(png_file)
            if svg_dir:
                os.makedirs(svg_dir, exist_ok=True)
            if png_dir:
                os.makedirs(png_dir, exist_ok=True)
            
            # Write SVG file
            with open(svg_file, 'w') as f:
                f.write(svg_content)
            print(f"✓ Generated {svg_file}")
            
            # Try to convert to PNG
            cmd = f"rsvg-convert -w 1200 --keep-aspect-ratio -f png -o '{png_file}' '{svg_file}'"
            result = os.system(cmd)
            
            if result == 0:
                print(f"✓ Generated {png_file}")
            else:
                print(f"⚠ Could not convert to PNG. Install librsvg2-bin for PNG conversion.")
            
        except Exception as e:
            print(f"Error generating visualization: {e}")
            # Don't fail the whole process if visualization fails
        
        return True
            
    except Exception as e:
        print(f"Error writing output file: {e}")
        return False

def process_all_traces():
    """Process all JSON trace files in the traces directory."""
    
    # Find all JSON files in traces directory (one level up)
    trace_files = glob.glob("../traces/*.json")
    
    if not trace_files:
        print("No trace files found in traces/ directory")
        return False
    
    print(f"Found {len(trace_files)} trace files to process:")
    for trace_file in trace_files:
        print(f"  - {trace_file}")
    print()
    
    # Create output directories
    os.makedirs("output/dbdiag_outputs", exist_ok=True)
    os.makedirs("output/visualizations", exist_ok=True)
    os.makedirs("output/images", exist_ok=True)
    
    success_count = 0
    
    for trace_file in trace_files:
        trace_name = os.path.splitext(os.path.basename(trace_file))[0]
        print(f"\n{'='*60}")
        print(f"Processing: {trace_file}")
        print(f"{'='*60}\n")
        
        # Generate output paths
        output_base = f"output/dbdiag_outputs/{trace_name}"
        svg_base = f"output/visualizations/{trace_name}"
        png_base = f"output/images/{trace_name}"
        
        # Process the file
        if process_single_file(trace_file, output_base):
            # Move visualization files to correct locations
            try:
                if os.path.exists(f"{output_base}.svg"):
                    os.rename(f"{output_base}.svg", f"{svg_base}.svg")
                if os.path.exists(f"{output_base}.png"):
                    os.rename(f"{output_base}.png", f"{png_base}.png")
                success_count += 1
            except Exception as e:
                print(f"Error moving visualization files: {e}")
        
    print(f"\n{'='*60}")
    print(f"Batch processing complete!")
    print(f"Successfully processed {success_count}/{len(trace_files)} trace files")
    print(f"\nOutput locations:")
    print(f"  - dbdiag format files: output/dbdiag_outputs/")
    print(f"  - SVG visualizations: output/visualizations/")
    print(f"  - PNG images: output/images/")
    print(f"{'='*60}")
    
    return success_count == len(trace_files)

def main():
    """Main function to handle the complete conversion."""
    
    # Check for help option
    if len(sys.argv) > 1 and sys.argv[1] in ['-h', '--help', 'help']:
        print("TLA+ to transaction_history.txt Converter")
        print("=" * 50)
        print("Usage: python tla_to_transaction_history.py [trace_file | all]")
        print()
        print("Arguments:")
        print("  trace_file   JSON trace file from ../traces/ directory")
        print("  all          Process all trace files in ../traces/ directory (default)")
        print()
        print("Output:")
        print("  output/dbdiag_outputs/<trace_name>.txt - dbdiag format files")
        print("  output/visualizations/<trace_name>.svg - SVG visualizations")
        print("  output/images/<trace_name>.png - PNG images")
        print()
        print("Supported input formats:")
        print("  - JSON trace files (.json files) - preferred")
        print("  - TLA+ model checker text output (.out files)")
        print()
        print("Available trace files:")
        print("  - ../traces/trace-GSingle2Inv2NodeCycleRWWW.json")
        print("  - ../traces/trace-ThreeNodeCycle.json")
        print()
        print("Examples:")
        print("  python tla_to_transaction_history.py                               # Process all traces")
        print("  python tla_to_transaction_history.py all                           # Process all traces")
        print("  python tla_to_transaction_history.py ../traces/trace-ThreeNodeCycle.json  # Process specific file")
        return
    
    # Handle arguments - only process trace files from traces directory
    if len(sys.argv) == 1:
        # Default: process all trace files
        success = process_all_traces()
    elif len(sys.argv) == 2:
        if sys.argv[1] == "all":
            # Process all trace files
            success = process_all_traces()
        else:
            # Process specific trace file
            input_file = sys.argv[1]
            # Extract base name for output files
            trace_name = os.path.splitext(os.path.basename(input_file))[0]
            output_base = f"output/dbdiag_outputs/{trace_name}"
            success = process_single_file(input_file, output_base)
    else:
        print("Usage: python tla_to_transaction_history.py [trace_file | all]")
        print("Use --help for more information.")
        sys.exit(1)
    
    if not success:
        sys.exit(1)

if __name__ == "__main__":
    main()
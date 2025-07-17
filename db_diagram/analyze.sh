#!/bin/bash
# Snapshot Isolation Analysis Helper Script

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

print_header() {
    echo -e "${BLUE}================================================${NC}"
    echo -e "${BLUE}  Snapshot Isolation Transaction Analysis${NC}"
    echo -e "${BLUE}================================================${NC}"
    echo
}

print_usage() {
    echo "Usage: $0 [command]"
    echo
    echo "Commands:"
    echo "  analyze    - Process all trace files and generate visualizations"
    echo "  clean      - Clean up generated output files"
    echo "  help       - Show this help message"
    echo
    echo "Examples:"
    echo "  $0 analyze    # Process all traces (default)"
    echo "  $0 clean      # Clean generated files"
}

analyze_all() {
    echo -e "${GREEN}🔍 Processing all trace files...${NC}"
    python3 tla_to_transaction_history.py all
    echo
    echo -e "${GREEN}✅ Analysis complete!${NC}"
    echo -e "${YELLOW}📁 Check outputs in:${NC}"
    echo "   • output/dbdiag_outputs/ - Transaction history files"
    echo "   • output/visualizations/ - SVG timeline visualizations"  
    echo "   • output/images/ - PNG timeline images"
}


clean_outputs() {
    echo -e "${YELLOW}🧹 Cleaning up generated files...${NC}"
    rm -rf output/
    echo -e "${GREEN}✅ Cleanup complete!${NC}"
}

# Main script logic
case "${1:-analyze}" in
    analyze)
        print_header
        analyze_all
        ;;
    clean)
        print_header
        clean_outputs
        ;;
    help|-h|--help)
        print_header
        print_usage
        ;;
    *)
        print_header
        echo -e "${RED}❌ Unknown command: $1${NC}"
        echo
        print_usage
        exit 1
        ;;
esac
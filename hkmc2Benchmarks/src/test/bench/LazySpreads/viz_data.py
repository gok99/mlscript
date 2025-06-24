#!/usr/bin/python3

# Generate diagrams from the lazy spreads benchmark json results
# 
import streamlit as st
import json
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
from plotly.subplots import make_subplots

def load_benchmark_data(file_paths):
    """Load benchmark data from JSON files"""
    all_data = []
    
    for file_path in file_paths:
        try:
            with open(file_path, 'r') as f:
                data = json.load(f)
            
            # Extract filename without extension for labeling
            filename = file_path.split('/')[-1].replace('.json', '')
            
            # Handle both single benchmark and array of benchmarks
            if isinstance(data, list):
                benchmarks = data
            else:
                benchmarks = [data]
            
            for benchmark in benchmarks:
                all_data.append({
                    'name': benchmark['name'],
                    'filename': filename,
                    'label': f"{benchmark['name']}#{filename}",
                    'mean_ms': benchmark['stats']['mean'] * 1000,  # Convert to milliseconds
                    'moe_ms': benchmark['stats']['moe'] * 1000,    # Convert to milliseconds
                    'sem_ms': benchmark['stats']['sem'] * 1000,    # Convert to milliseconds
                    'hz': benchmark.get('hz', 0)
                })
        
        except Exception as e:
            st.error(f"Error loading {file_path}: {str(e)}")
    
    return pd.DataFrame(all_data)

def create_bar_chart(df, selected_benchmarks):
    """Create bar chart with error bars for selected benchmarks"""
    # Filter data based on selection
    filtered_df = df[df['label'].isin(selected_benchmarks)]
    
    if filtered_df.empty:
        return None
    
    fig = go.Figure()
    
    # Add bars with error bars
    fig.add_trace(go.Bar(
        x=filtered_df['label'],
        y=filtered_df['mean_ms'],
        error_y=dict(
            type='data',
            array=filtered_df['moe_ms'],
            visible=True,
            color='red',
            thickness=2,
            width=3
        ),
        name='Mean Time (ms)',
        text=[f'{val:.4f} ms' for val in filtered_df['mean_ms']],
        textposition='outside',
        hovertemplate='<b>%{x}</b><br>' +
                      'Mean Time: %{y:.4f} ms<br>' +
                      'Margin of Error: %{error_y.array:.4f} ms<br>' +
                      '<extra></extra>'
    ))
    
    # Update layout
    fig.update_layout(
        title='Benchmark Results - Mean Execution Time with Error Bars',
        xaxis_title='Benchmark (name#filename)',
        yaxis_title='Time (milliseconds)',
        xaxis=dict(tickangle=45),
        height=600,
        showlegend=False,
        template='plotly_white'
    )
    
    return fig

def main():
    st.set_page_config(
        page_title="Benchmark Results",
        page_icon="📊",
        layout="wide"
    )
    
    st.title("📊 Benchmark Results Visualization")
    st.markdown("Upload your JSON benchmark files to visualize execution times with error bars.")
    
    # File upload section
    st.sidebar.header("File Upload")
    uploaded_files = st.sidebar.file_uploader(
        "Choose JSON files",
        type="json",
        accept_multiple_files=True,
        help="Upload up to 3 JSON files containing benchmark data"
    )
    
    # Alternative: Manual file path input for local files
    st.sidebar.header("Or Use Local Files")
    use_local_files = st.sidebar.checkbox("Use local file paths")
    
    if use_local_files:
        file_paths = []
        for i in range(3):
            path = st.sidebar.text_input(f"File {i+1} path:", key=f"path_{i}")
            if path:
                file_paths.append(path)
    
    # Process files
    df = None
    
    if uploaded_files:
        # Process uploaded files
        all_data = []
        for uploaded_file in uploaded_files:
            try:
                data = json.load(uploaded_file)
                filename = uploaded_file.name.replace('.json', '')
                
                # Handle both single benchmark and array of benchmarks
                if isinstance(data, list):
                    benchmarks = data
                else:
                    benchmarks = [data]
                
                for benchmark in benchmarks:
                    all_data.append({
                        'name': benchmark['name'],
                        'filename': filename,
                        'label': f"{benchmark['name']}#{filename}",
                        'mean_ms': benchmark['stats']['mean'] * 1000,
                        'moe_ms': benchmark['stats']['moe'] * 1000,
                        'sem_ms': benchmark['stats']['sem'] * 1000,
                        'hz': benchmark.get('hz', 0)
                    })
            
            except Exception as e:
                st.error(f"Error processing {uploaded_file.name}: {str(e)}")
        
        df = pd.DataFrame(all_data)
    
    elif use_local_files and file_paths:
        # Process local files
        df = load_benchmark_data(file_paths)
    
    else:
        # Show example with placeholder data
        st.info("Upload JSON files or provide local file paths to see your benchmark results.")
        
        # Create example data
        example_data = [
            {'name': 'buildLazy', 'filename': 'benchmark1', 'label': 'buildLazy#benchmark1', 
             'mean_ms': 0.176, 'moe_ms': 0.0025, 'sem_ms': 0.00128, 'hz': 5676},
            {'name': 'processData', 'filename': 'benchmark1', 'label': 'processData#benchmark1', 
             'mean_ms': 0.234, 'moe_ms': 0.0034, 'sem_ms': 0.00174, 'hz': 4274},
            {'name': 'renderComponent', 'filename': 'benchmark1', 'label': 'renderComponent#benchmark1', 
             'mean_ms': 0.198, 'moe_ms': 0.0029, 'sem_ms': 0.00148, 'hz': 5051},
            {'name': 'buildLazy', 'filename': 'benchmark2', 'label': 'buildLazy#benchmark2', 
             'mean_ms': 0.182, 'moe_ms': 0.0028, 'sem_ms': 0.00143, 'hz': 5495},
            {'name': 'processData', 'filename': 'benchmark2', 'label': 'processData#benchmark2', 
             'mean_ms': 0.219, 'moe_ms': 0.0031, 'sem_ms': 0.00158, 'hz': 4566},
        ]
        df = pd.DataFrame(example_data)
        st.warning("Showing example data. Upload your files to see actual results.")
    
    if df is not None and not df.empty:
        # Benchmark selection
        st.subheader("Select Benchmarks to Display")
        available_benchmarks = df['label'].tolist()
        
        # Create selection interface
        col1, col2 = st.columns([3, 1])
        with col1:
            selected_benchmarks = st.multiselect(
                "Choose which benchmarks to show in the chart:",
                options=available_benchmarks,
                default=available_benchmarks,  # All selected by default
                help="Select/deselect benchmarks to customize the chart view"
            )
        
        with col2:
            if st.button("Select All"):
                selected_benchmarks = available_benchmarks
            if st.button("Clear All"):
                selected_benchmarks = []
        
        # Display the chart
        if selected_benchmarks:
            fig = create_bar_chart(df, selected_benchmarks)
            if fig:
                st.plotly_chart(fig, use_container_width=True)
        else:
            st.warning("Please select at least one benchmark to display the chart.")
        
        # Display summary statistics by file
        st.subheader("Summary Statistics by File")
        
        # Get unique filenames
        unique_files = df['filename'].unique()
        
        # Create tabs for each file
        tabs = st.tabs([f"File: {filename}" for filename in unique_files])
        
        for i, filename in enumerate(unique_files):
            with tabs[i]:
                file_data = df[df['filename'] == filename]
                
                # Calculate statistics for this file
                stats_data = []
                for _, row in file_data.iterrows():
                    stats_data.append({
                        'Benchmark': row['name'],
                        'Mean (ms)': f"{row['mean_ms']:.4f}",
                        'MOE (ms)': f"{row['moe_ms']:.4f}",
                        'SEM (ms)': f"{row['sem_ms']:.4f}",
                        'Frequency (Hz)': f"{row['hz']:.2f}" if row['hz'] > 0 else "N/A"
                    })
                
                stats_df = pd.DataFrame(stats_data)
                st.dataframe(stats_df, use_container_width=True)
                
                # File summary
                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("Total Benchmarks", len(file_data))
                with col2:
                    avg_time = file_data['mean_ms'].mean()
                    st.metric("Average Time", f"{avg_time:.4f} ms")
                with col3:
                    if file_data['hz'].sum() > 0:
                        avg_hz = file_data['hz'].mean()
                        st.metric("Average Frequency", f"{avg_hz:.2f} Hz")
        
        # Raw data table
        st.subheader("Raw Data")
        display_df = df[['label', 'mean_ms', 'moe_ms', 'sem_ms', 'hz']].copy()
        display_df.columns = ['Benchmark', 'Mean (ms)', 'MOE (ms)', 'SEM (ms)', 'Hz']
        st.dataframe(display_df, use_container_width=True)

if __name__ == "__main__":
    main()
